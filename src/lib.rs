pub mod cnf;
mod lit_set;
mod var_data;

use lit_set::LitSet;
use var_data::VarData;

const VAR_DECAY: f32 = 0.95;
const RESTART_INTERVAL_MULTIPLIER: usize = 100;
const RESCALE_THRESHOLD: f32 = 1e30;

pub type ClauseId = usize;

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(u16);

const SIGN_BIT: u16 = 1 << (u16::BITS - 1);
const VAR_MASK: u16 = !SIGN_BIT;

impl Lit {
    #[inline]
    pub fn new(var: u16, val: bool) -> Self {
        if val { Lit::pos(var) } else { Lit::neg(var) }
    }

    #[inline]
    pub fn pos(var: u16) -> Self {
        debug_assert!(var < VAR_MASK);
        Lit(var | SIGN_BIT)
    }

    #[inline]
    pub fn neg(var: u16) -> Self {
        debug_assert!(var < VAR_MASK);
        Lit(var)
    }

    #[inline]
    pub fn negated(self) -> Self {
        Lit(self.0 ^ SIGN_BIT)
    }

    #[inline]
    pub fn var(self) -> usize {
        (self.0 & VAR_MASK) as usize
    }

    #[inline]
    pub fn val(self) -> bool {
        (self.0 & SIGN_BIT) != 0
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
    var: u16,
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

#[derive(Debug)]
pub struct Solver {
    num_vars: usize,
    var_data: VarData,
    clauses: Vec<Clause>,
    clause_deleted: Vec<bool>,
    clause_lbds: Vec<u16>,
    // states
    trail: Vec<Assignment>,
    decision_level_starts: Vec<usize>,
    decision_level: usize,
    propagation_head: usize,
}

enum ClauseResult {
    WatchKept,
    WatchMoved(Lit),
    Conflict,
    Unit(Lit),
}

impl Solver {
    pub fn new(num_vars: usize, clauses: Vec<Vec<Lit>>) -> Self {
        let mut solver = Solver {
            //variables
            num_vars,
            var_data: VarData::new(num_vars),
            // clauses
            clauses: Vec::new(),
            clause_deleted: Vec::new(),
            clause_lbds: Vec::new(),
            // solver states
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
        let clause = &mut self.clauses[cid];

        if clause[0] != falsified {
            clause.swap(0, 1);
        }

        debug_assert!(clause[0] == falsified || clause[1] != falsified);

        let other = clause[1];

        if self.var_data.assigned_val_of(other) == Some(true) {
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

        match self.var_data.assigned_val_of(other) {
            Some(false) => ClauseResult::Conflict,
            None => ClauseResult::Unit(other),
            Some(true) => unreachable!(),
        }
    }

    fn propagate_literal(&mut self, falsified: Lit) -> Option<ClauseId> {
        let mut i = 0;
        while i < self.var_data.watched_clause(falsified).len() {
            let cid = self.var_data.watched_clause(falsified)[i];

            if self.clause_deleted[cid] {
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
            self.var_data.unassign(assignment.var as usize);
        }

        self.decision_level_starts.truncate(target_level + 1);
        self.propagation_head = self.trail.len();
        self.decision_level = target_level;
    }

    fn analyze_conflict(&mut self, cid: ClauseId) -> (Vec<Lit>, u16, Lit, usize) {
        let mut learned = LitSet::new(&self.clauses[cid], self);
        let start = *self.decision_level_starts.last().unwrap();
        let current_level_assignments = &self.trail[start..];

        for assignment in current_level_assignments.iter().rev() {
            if learned.num_current_level == 1 {
                break;
            }

            let pivot = assignment.var;

            if !learned.contains(Lit::pos(pivot)) && !learned.contains(Lit::neg(pivot)) {
                continue;
            }

            let Reason::Deduced(cid) = assignment.reason else {
                continue;
            };

            for &lit in &self.clauses[cid] {
                self.var_data.bump_activity(lit.var());
            }

            learned.extend(&self.clauses[cid], self);
            learned.remove(Lit::pos(pivot), self);
            learned.remove(Lit::neg(pivot), self);
        }

        debug_assert!(learned.num_current_level == 1);

        learned.simplify(self);
        learned.into_analysis_result(self)
    }

    fn add_clause(&mut self, clause: Vec<Lit>, lbd: u16) -> Option<usize> {
        if clause.len() == 1 {
            self.assign(clause[0], Reason::Fixed);
            return None;
        }

        let cid = self.clauses.len();
        self.var_data.register(&clause, cid);
        self.clauses.push(clause);
        self.clause_deleted.push(false);
        self.clause_lbds.push(lbd);

        Some(cid)
    }

    fn assign(&mut self, lit: Lit, reason: Reason) {
        let assignment = self.var_data.assign(lit, reason, self.decision_level);
        self.trail.push(assignment);
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

            if num_restart % 50 == 0 {
                for cid in 0..self.clauses.len() {
                    if self.clause_lbds[cid] > 7 {
                        self.clause_deleted[cid] = true;
                    }
                }
            }

            self.backjump(0);
        }

        unreachable!()
    }

    fn assignment_of(&self, lit: Lit) -> &Assignment {
        self.var_data.assignment_of(lit.var())
    }

    pub fn value_of(&self, var: usize) -> Option<bool> {
        self.var_data.assigned_val_of(Lit::pos(var as u16))
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
