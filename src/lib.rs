pub mod cnf;
mod lit_set;

use lit_set::LitSet;

const VAR_DECAY: f32 = 0.95;
const RESTART_INTERVAL_MULTIPLIER: usize = 100;
const RESCALE_THRESHOLD: f32 = 1e30;

pub type ClauseId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit {
    var: usize,
    val: bool,
}

impl Lit {
    pub fn pos(var: usize) -> Self {
        Lit { var, val: true }
    }
    pub fn neg(var: usize) -> Self {
        Lit { var, val: false }
    }

    pub fn negated(self) -> Self {
        Lit {
            var: self.var,
            val: !self.val,
        }
    }

    fn to_index(self, num_vars: usize) -> usize {
        if self.val {
            num_vars + self.var
        } else {
            self.var
        }
    }
}

pub type Clause = Vec<Lit>;

#[derive(Debug, Clone)]
enum Reason {
    Decided,
    Deduced(ClauseId),
}

#[derive(Debug, Clone)]
struct Assignment {
    lit: Lit,
    level: usize,
    reason: Reason,
}

impl Assignment {
    fn var(&self) -> usize {
        self.lit.var
    }

    fn val(&self) -> bool {
        self.lit.val
    }
}

#[derive(Debug)]
pub struct Solver {
    num_vars: usize,
    var_data: VarData,
    clauses: Vec<Clause>,
    // states
    trail: Vec<Assignment>,
    decision_level_starts: Vec<usize>,
    decision_level: usize,
    propagation_head: usize,
}

#[derive(Debug)]
struct VarData {
    num_vars: usize,
    activity_inc: f32,
    assignments: Vec<Option<Assignment>>,
    activities: Vec<f32>,
    saved_polarities: Vec<bool>,
    watched_clauses: Vec<Vec<ClauseId>>,
}

impl VarData {
    fn new(num_vars: usize) -> Self {
        VarData {
            num_vars,
            activity_inc: 1.,
            assignments: vec![None; num_vars],
            activities: vec![0.; num_vars],
            saved_polarities: vec![true; num_vars],
            watched_clauses: vec![Vec::new(); 2 * num_vars],
        }
    }

    fn assign(&mut self, lit: Lit, reason: Reason, level: usize) -> Assignment {
        debug_assert!(self.assignments[lit.var].is_none());
        let assignment = Assignment { lit, level, reason };
        self.assignments[lit.var] = Some(assignment.clone());
        self.saved_polarities[lit.var] = lit.val;
        assignment
    }

    fn register(&mut self, clause: &Vec<Lit>, cid: usize) {
        debug_assert!(clause.len() >= 2);
        for lit in clause {
            self.activities[lit.var] += 1.;
        }
        self.watched_clauses[clause[0].to_index(self.num_vars)].push(cid);
        self.watched_clauses[clause[1].to_index(self.num_vars)].push(cid);
    }

    fn unassign(&mut self, var: usize) {
        self.assignments[var] = None;
    }

    fn bump_activity(&mut self, var: usize) {
        self.activities[var] += self.activity_inc;

        if self.activities[var] > RESCALE_THRESHOLD {
            self.activity_inc /= RESCALE_THRESHOLD;
            for a in &mut self.activities {
                *a /= RESCALE_THRESHOLD;
            }
        }
    }

    fn decay_activities(&mut self) {
        self.activity_inc /= VAR_DECAY;
    }

    fn pick_branch_lit(&self) -> Option<Lit> {
        let var = (0..self.num_vars)
            .filter(|&v| self.assignments[v].is_none())
            .max_by(|&u, &v| {
                self.activities[u]
                    .partial_cmp(&self.activities[v])
                    .unwrap_or(std::cmp::Ordering::Equal)
            })?;

        Some(Lit {
            var,
            val: self.saved_polarities[var],
        })
    }

    fn get_assigned_val(&self, lit: Lit) -> Option<bool> {
        match &self.assignments[lit.var] {
            Some(assignment) if assignment.val() == lit.val => Some(true),
            Some(_) => Some(false),
            None => None,
        }
    }
}

impl Solver {
    pub fn new(num_vars: usize, clauses: Vec<Vec<Lit>>) -> Self {
        let mut solver = Solver {
            //variables
            num_vars,
            var_data: VarData::new(num_vars),
            // clauses
            clauses: Vec::new(),
            // states
            trail: Vec::new(),
            decision_level_starts: vec![0],
            decision_level: 0,
            propagation_head: 0,
        };

        for clause in clauses {
            solver.add_clause(clause);
        }

        solver
    }

    fn propagate(&mut self) -> Option<ClauseId> {
        while self.trail.len() > self.propagation_head {
            let lit_negated = self.trail[self.propagation_head].lit.negated();
            let lit_negated_index = lit_negated.to_index(self.num_vars);

            let mut i = 0;
            while i < self.var_data.watched_clauses[lit_negated_index].len() {
                let cid = self.var_data.watched_clauses[lit_negated_index][i];
                let clause = &mut self.clauses[cid];

                debug_assert!(clause[0] == lit_negated || clause[1] == lit_negated);

                if clause[0] != lit_negated {
                    clause.swap(0, 1);
                }

                let other_watched = clause[1];
                if self.var_data.get_assigned_val(other_watched) == Some(true) {
                    i += 1;
                    continue;
                }

                let mut found = false;
                for (pos, lit) in clause[2..].iter().enumerate() {
                    if self.var_data.get_assigned_val(*lit) != Some(false) {
                        debug_assert_ne!(*lit, clause[1]);
                        self.var_data.watched_clauses[lit_negated_index].swap_remove(i);
                        self.var_data.watched_clauses[lit.to_index(self.num_vars)].push(cid);
                        clause.swap(0, pos + 2);

                        found = true;
                        break;
                    }
                }

                if !found {
                    match self.var_data.get_assigned_val(other_watched) {
                        Some(true) => unreachable!(),
                        Some(false) => return Some(cid),
                        None => self.assign(other_watched, Reason::Deduced(cid)),
                    }
                    i += 1;
                }
            }

            self.propagation_head += 1;
        }

        None
    }

    fn backjump(&mut self, target_level: usize) {
        if target_level == self.decision_level {
            return;
        }

        let cut = self.decision_level_starts[target_level + 1];

        for assignment in self.trail.drain(cut..) {
            self.var_data.unassign(assignment.var());
        }

        self.decision_level_starts.truncate(target_level + 1);
        self.propagation_head = self.trail.len();
        self.decision_level = target_level;
    }

    fn analyze_conflict(&mut self, cid: ClauseId) -> (Vec<Lit>, Lit, usize) {
        let mut learned = LitSet::new(&self.clauses[cid], self);
        let start = *self.decision_level_starts.last().unwrap();
        let current_level_assignments = &self.trail[start..];

        for assignment in current_level_assignments.iter().rev() {
            if learned.num_current_level == 1 {
                break;
            }

            let pivot = assignment.var();

            if !learned.contains(&Lit::pos(pivot)) && !learned.contains(&Lit::neg(pivot)) {
                continue;
            }

            let Reason::Deduced(cid) = assignment.reason else {
                continue;
            };

            for &lit in &self.clauses[cid] {
                self.var_data.bump_activity(lit.var);
            }

            learned.extend(&self.clauses[cid], self);
            learned.remove(&Lit::pos(pivot), self);
            learned.remove(&Lit::neg(pivot), self);
        }

        debug_assert!(learned.num_current_level == 1);

        learned.simplify(self);
        learned.into_analysis_result(self)
    }

    fn add_clause(&mut self, mut clause: Vec<Lit>) {
        let cid = self.clauses.len();

        clause.sort_unstable();
        clause.dedup();

        if clause.len() == 1 {
            self.assign(clause[0], Reason::Deduced(cid))
        } else {
            self.var_data.register(&clause, cid);
        }

        self.clauses.push(clause);
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

                    let (learned_clause, asserted_lit, backjump_level) =
                        self.analyze_conflict(conflict_cid);

                    self.add_clause(learned_clause);

                    debug_assert!(backjump_level < self.decision_level);
                    self.backjump(backjump_level);

                    self.assign(asserted_lit, Reason::Deduced(self.clauses.len() - 1));

                    self.var_data.decay_activities()
                } else {
                    let Some(lit) = self.var_data.pick_branch_lit() else {
                        return true;
                    };
                    self.decision_level += 1;
                    self.decision_level_starts.push(self.trail.len());
                    self.assign(lit, Reason::Decided)
                }
            }

            self.backjump(0);
        }

        unreachable!()
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
