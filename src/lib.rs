mod clause_data;
pub mod cnf;
mod lit_set;
mod var_data;

use clause_data::ClauseData;
pub use cnf::CNF;
use lit_set::LitSet;
use var_data::VarData;

const VAR_DECAY: f32 = 0.99;
const RESTART_INTERVAL_MULTIPLIER: usize = 100;
const RESCALE_THRESHOLD: f32 = 1e30;
const CLAUSE_REDUCTION_INTERVAL: usize = 50;
const RECIP_REDUCTION_RATIO: usize = 2;
const COMPACTION_INTERVAL: usize = 100;

pub type ClauseId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(usize);

const VAR_MASK: usize = !1;

impl Lit {
    pub fn new(var: usize, val: bool) -> Self {
        if val { Lit::pos(var) } else { Lit::neg(var) }
    }

    pub fn pos(var: usize) -> Self {
        debug_assert!(var < VAR_MASK);
        Lit(var << 1 | 1)
    }

    pub fn neg(var: usize) -> Self {
        debug_assert!(var < VAR_MASK);
        Lit(var << 1)
    }

    pub fn negated(self) -> Self {
        Lit(self.0 ^ 1)
    }

    pub fn var(self) -> usize {
        (self.0 & VAR_MASK) >> 1
    }

    pub fn val(self) -> bool {
        (self.0 & 1) != 0
    }
}

pub type Clause = Vec<Lit>;

#[derive(Debug, Clone)]
enum Reason {
    Guessed,
    Deduced(ClauseId),
    Fixed,
}

#[derive(Debug, Clone)]
struct Assignment {
    var: usize,
    val: bool,
    level: usize,
    reason: Reason,
}

impl Assignment {
    fn falsified(&self) -> Lit {
        if self.val {
            Lit::neg(self.var)
        } else {
            Lit::pos(self.var)
        }
    }
}

enum ClauseResult {
    WatchKept,
    WatchMoved(Lit),
    Conflict,
    Unit(Lit),
}

#[derive(Debug)]
pub struct Solver {
    num_vars: usize,
    var_data: VarData,
    clause_data: ClauseData,
    fixed_literals: Vec<Lit>,
    // states
    trail: Vec<Assignment>,
    decision_level_starts: Vec<usize>,
    decision_level: usize,
    propagation_head: usize,
}

impl Solver {
    pub fn new(num_vars: usize, clauses: Vec<Vec<Lit>>) -> Self {
        let mut solver = Solver {
            num_vars,
            var_data: VarData::new(num_vars),
            clause_data: ClauseData::new(),
            fixed_literals: Vec::new(),
            // states
            trail: Vec::new(),
            decision_level_starts: vec![0],
            decision_level: 0,
            propagation_head: 0,
        };

        for clause in clauses {
            solver.add_clause(clause, 0);
        }

        solver
    }

    fn propagate_clause(&mut self, cid: ClauseId, falsified: Lit) -> ClauseResult {
        let clause = self.clause_data.get_mut(cid);

        if clause[0] != falsified {
            clause.swap(0, 1);
        }

        debug_assert!(clause[0] == falsified || clause[1] != falsified);

        let other = clause[1];

        let assigned_val_of_other = self.var_data.assigned_val_of(other);

        if assigned_val_of_other == Some(true) {
            return ClauseResult::WatchKept;
        }

        for i in 2..clause.len() {
            let lit = clause[i];

            if self.var_data.assigned_val_of(lit) != Some(false) {
                debug_assert_ne!(lit, other);
                clause.swap(0, i);
                return ClauseResult::WatchMoved(lit);
            }
        }

        match assigned_val_of_other {
            Some(true) => unreachable!(),
            Some(false) => ClauseResult::Conflict,
            None => ClauseResult::Unit(other),
        }
    }

    fn propagate_literal(&mut self, falsified: Lit) -> Option<ClauseId> {
        let mut i = 0;
        while i < self.var_data.watched_clause(falsified).len() {
            let cid = self.var_data.watched_clause(falsified)[i];

            if self.clause_data.deleted(cid) {
                self.var_data.watched_clause(falsified).swap_remove(i);
                continue;
            }

            match self.propagate_clause(cid, falsified) {
                ClauseResult::WatchKept => {
                    i += 1;
                }
                ClauseResult::WatchMoved(new_lit) => {
                    self.var_data.watched_clause(falsified).swap_remove(i);
                    self.var_data.watched_clause(new_lit).push(cid);
                }
                ClauseResult::Conflict => {
                    return Some(cid);
                }
                ClauseResult::Unit(unit_lit) => {
                    self.assign(unit_lit, Reason::Deduced(cid));
                    i += 1;
                }
            }
        }

        None
    }

    fn propagate(&mut self) -> Option<ClauseId> {
        while self.trail.len() > self.propagation_head {
            let falsified = self.trail[self.propagation_head].falsified();
            self.propagation_head += 1;

            if let Some(conflict) = self.propagate_literal(falsified) {
                return Some(conflict);
            }
        }

        None
    }

    fn backjump(&mut self, target_level: usize) {
        if target_level == self.decision_level {
            return;
        }

        let cut = self.decision_level_starts[target_level + 1];

        for assignment in self.trail.drain(cut..) {
            self.var_data.unassign(assignment.var);
            if let Reason::Deduced(cid) = assignment.reason {
                self.clause_data.unlock(cid);
            }
        }

        self.decision_level_starts.truncate(target_level + 1);
        self.propagation_head = self.trail.len();
        self.decision_level = target_level;
    }

    fn analyze_conflict(&mut self, cid: ClauseId) -> (Clause, u16, Lit, usize) {
        let start = *self.decision_level_starts.last().unwrap();
        let current_level_assignments = &self.trail[start..];

        let mut learned = LitSet::new(self.num_vars);
        let mut num_current_level = 0;

        for &lit in self.clause_data.get(cid) {
            learned.push(lit);
            let assignment = self.var_data.assignment_of(lit.var());
            if assignment.level == self.decision_level {
                num_current_level += 1;
            }
            self.var_data.bump_activity(lit.var());
        }

        for assignment in current_level_assignments.iter().rev() {
            if num_current_level == 1 {
                break;
            }

            let pivot = assignment.var;

            if !learned.contains(pivot) {
                continue;
            }

            let Reason::Deduced(cid) = assignment.reason else {
                continue;
            };

            for &lit in self.clause_data.get(cid) {
                if learned.push(lit) {
                    let assignment = self.var_data.assignment_of(lit.var());
                    if assignment.level == self.decision_level {
                        num_current_level += 1;
                    }
                }
                self.var_data.bump_activity(lit.var());
            }

            if learned.remove(pivot)
                && self.var_data.assignment_of(pivot).level == self.decision_level
            {
                num_current_level -= 1;
            }
        }

        debug_assert!(num_current_level == 1);

        learned.simplify(&self.var_data, &self.clause_data);

        let learned = learned.into_vec();

        let mut asserted_lit = Lit::pos(0); // placeholder to be overwritten
        let mut backjump_level = 0;
        let mut seen_levels = vec![false; self.decision_level + 1];

        for &lit in &learned {
            let level = self.var_data.assignment_of(lit.var()).level;

            if level == self.decision_level {
                asserted_lit = lit;
            } else {
                backjump_level = backjump_level.max(level);
            }

            seen_levels[level] = true;
        }

        let lbd = seen_levels.iter().filter(|&seen| *seen).count() as u16;
        (learned, lbd, asserted_lit, backjump_level)
    }

    fn add_clause(&mut self, clause: Clause, lbd: u16) -> Option<usize> {
        if clause.len() == 1 {
            self.assign(clause[0], Reason::Fixed);
            self.fixed_literals.push(clause[0]);
            return None;
        }

        let cid = self.clause_data.len();
        self.var_data.register(&clause, cid);
        self.clause_data.push(clause, false, lbd);

        Some(cid)
    }

    fn assign(&mut self, lit: Lit, reason: Reason) {
        if let Reason::Deduced(cid) = reason {
            self.clause_data.lock(cid);
        }

        let assignment = self.var_data.assign(lit, self.decision_level, reason);
        self.trail.push(assignment);
    }

    fn compact(&mut self) {
        self.clause_data.compact();

        self.trail.clear();
        self.decision_level_starts.drain(1..);
        self.propagation_head = 0;

        self.var_data.clear();

        for &lit in &self.fixed_literals {
            let assignment = self.var_data.assign(lit, 0, Reason::Fixed);
            self.trail.push(assignment);
        }

        for (cid, clause) in self.clause_data.iter().enumerate() {
            self.var_data.register(clause, cid)
        }
    }

    pub fn solve(&mut self) -> bool {
        for num_restart in 0.. {
            for _t in 0..restart_interval(num_restart) {
                if let Some(conflict_cid) = self.propagate() {
                    if self.decision_level == 0 {
                        return false;
                    }

                    let (learned_clause, lbd, asserted_lit, backjump_level) =
                        self.analyze_conflict(conflict_cid);

                    debug_assert!(backjump_level < self.decision_level);
                    self.backjump(backjump_level);

                    if let Some(cid) = self.add_clause(learned_clause, lbd) {
                        self.assign(asserted_lit, Reason::Deduced(cid));
                    }

                    self.var_data.decay_activities();
                } else {
                    let Some(lit) = self.var_data.pick_branch_lit() else {
                        return true;
                    };
                    self.decision_level += 1;
                    self.decision_level_starts.push(self.trail.len());
                    self.assign(lit, Reason::Guessed)
                }
            }

            self.backjump(0);

            if num_restart % CLAUSE_REDUCTION_INTERVAL == 0 {
                self.clause_data.reduce();
            }

            if num_restart % COMPACTION_INTERVAL == 0 {
                self.compact();
            }
        }

        unreachable!()
    }

    pub fn value_of(&self, var: usize) -> Option<bool> {
        self.var_data.assigned_val_of(Lit::pos(var))
    }
}

fn restart_interval(num_restart: usize) -> usize {
    RESTART_INTERVAL_MULTIPLIER * luby(num_restart)
}

fn luby(mut i: usize) -> usize {
    let mut size = 1;
    let mut seq = 0;

    while size < i + 1 {
        seq += 1;
        size = 2 * size + 1;
    }

    while size - 1 != i {
        size = (size - 1) / 2;
        seq -= 1;
        i %= size;
    }

    2_usize.pow(seq)
}
