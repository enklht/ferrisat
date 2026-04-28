pub mod cnf;
mod lit_set;

use lit_set::LitSet;

const VAR_DECAY: f32 = 0.95;
const RESTART_INTERVAL_MULTIPLIER: usize = 100;
const RESCALE_THRESHOLD: f32 = 1e30;

fn bump_activity(var: usize, activities: &mut [f32], var_inc: &mut f32) {
    activities[var] += *var_inc;

    if activities[var] > RESCALE_THRESHOLD {
        *var_inc /= RESCALE_THRESHOLD;
        for a in activities {
            *a /= RESCALE_THRESHOLD;
        }
    }
}

pub type ClauseId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone)]

enum ClauseState {
    Satisfied,
    Conflict,
    Unit(Lit),
    Unresolved,
}

#[derive(Debug)]
pub struct Solver {
    num_vars: usize,
    clauses: Vec<Clause>,
    assignments: Vec<Option<Assignment>>,
    saved_polarities: Vec<bool>,
    var_inc: f32,
    activities: Vec<f32>,
    trail: Vec<Assignment>,
    trail_lim: Vec<usize>,
    decision_level: usize,
}

impl Solver {
    pub fn new(num_vars: usize, clauses: Vec<Clause>) -> Self {
        let mut activities = vec![0.; num_vars];
        let mut jw_weights = vec![0.; num_vars];
        for clause in &clauses {
            for lit in clause {
                activities[lit.var] += 1.;
                jw_weights[lit.var] += 2f32.powi(-(clause.len() as i32))
            }
        }
        let saved_polarities = jw_weights.iter().map(|&w| w >= 0.).collect();

        Solver {
            num_vars,
            clauses,
            assignments: vec![None; num_vars],
            saved_polarities,
            var_inc: 1.,
            activities,
            trail: Vec::new(),
            trail_lim: vec![0],
            decision_level: 0,
        }
    }

    fn clause_state(&self, cid: ClauseId) -> ClauseState {
        let mut found = None;

        for lit in &self.clauses[cid] {
            match &self.assignments[lit.var] {
                Some(assignment) if assignment.val() == lit.val => return ClauseState::Satisfied,
                Some(_) => {}
                None if found.is_some() => return ClauseState::Unresolved,
                None => found = Some(*lit),
            }
        }

        match found {
            Some(lit) => ClauseState::Unit(lit),
            None => ClauseState::Conflict,
        }
    }

    fn propagate(&mut self) -> Option<ClauseId> {
        let mut updated = true;

        while updated {
            updated = false;

            for cid in 0..self.clauses.len() {
                match self.clause_state(cid) {
                    ClauseState::Satisfied => {}
                    ClauseState::Conflict => return Some(cid),
                    ClauseState::Unit(lit) => {
                        self.assign(lit, Reason::Deduced(cid));
                        updated = true;
                    }
                    ClauseState::Unresolved => {}
                }
            }
        }

        None
    }

    fn backjump(&mut self, target_level: usize) {
        if target_level == self.decision_level {
            return;
        }

        let cut = self.trail_lim[target_level + 1];

        for assignment in self.trail.drain(cut..) {
            self.assignments[assignment.var()] = None;
        }

        self.trail_lim.truncate(target_level + 1);
        self.decision_level = target_level;
    }

    fn decay(&mut self) {
        self.var_inc /= VAR_DECAY;
    }

    fn analyze_conflict(&mut self, cid: ClauseId) -> (Clause, Lit, usize) {
        let mut learned = LitSet::new(&self.clauses[cid], self);
        let start = *self.trail_lim.last().unwrap();
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
                bump_activity(lit.var, &mut self.activities, &mut self.var_inc);
            }
            learned.extend(&self.clauses[cid], self);
            learned.remove(&Lit::pos(pivot), self);
            learned.remove(&Lit::neg(pivot), self);
        }

        debug_assert!(learned.num_current_level == 1);

        learned.simplify(self);
        learned.into_analysis_result(self)
    }

    fn pick_branch_lit(&self) -> Option<Lit> {
        use std::cmp::Ordering as O;
        let var = (0..self.num_vars)
            .filter(|&v| self.assignments[v].is_none())
            .max_by(|&u, &v| {
                self.activities[u]
                    .partial_cmp(&self.activities[v])
                    .unwrap_or(O::Equal)
            })?;

        Some(Lit {
            var,
            val: self.saved_polarities[var],
        })
    }

    fn assign(&mut self, lit: Lit, reason: Reason) {
        debug_assert!(self.assignments[lit.var].is_none());
        let assignment = Assignment {
            lit,
            level: self.decision_level,
            reason,
        };
        self.assignments[lit.var] = Some(assignment.clone());
        self.saved_polarities[lit.var] = lit.val;
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

                    self.clauses.push(learned_clause);

                    debug_assert!(backjump_level < self.decision_level);
                    self.backjump(backjump_level);

                    self.assign(asserted_lit, Reason::Deduced(self.clauses.len() - 1));

                    self.decay()
                } else {
                    let Some(lit) = self.pick_branch_lit() else {
                        return true;
                    };
                    self.decision_level += 1;
                    self.trail_lim.push(self.trail.len());
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
