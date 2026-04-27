use log::{debug, trace};
use rustc_hash::FxHashSet as HashSet;

pub mod cnf;

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
    trail: Vec<Assignment>,
    trail_lim: Vec<usize>,
    decision_level: usize,
}

impl Solver {
    fn lit_to_string(lit: Lit) -> String {
        if lit.val {
            format!("x{}", lit.var + 1)
        } else {
            format!("~x{}", lit.var + 1)
        }
    }

    fn clause_to_string(clause: &Clause) -> String {
        clause
            .iter()
            .copied()
            .map(Self::lit_to_string)
            .collect::<Vec<_>>()
            .join(" v ")
    }

    fn learned_to_string(learned: &HashSet<Lit>) -> String {
        let mut lits: Vec<_> = learned.iter().copied().collect();
        lits.sort_by_key(|lit| (lit.var, lit.val));
        lits.into_iter()
            .map(Self::lit_to_string)
            .collect::<Vec<_>>()
            .join(" v ")
    }

    pub fn new(num_vars: usize, clauses: Vec<Clause>) -> Self {
        Solver {
            num_vars,
            clauses,
            assignments: vec![None; num_vars],
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
                    ClauseState::Conflict => {
                        debug!(
                            "conflict in clause c{}: ({})",
                            cid,
                            Self::clause_to_string(&self.clauses[cid])
                        );
                        return Some(cid);
                    }
                    ClauseState::Unit(lit) => {
                        debug!(
                            "unit from c{}: ({}) => {}",
                            cid,
                            Self::clause_to_string(&self.clauses[cid]),
                            Self::lit_to_string(lit)
                        );
                        self.assign(lit, Reason::Deduced(cid));
                        updated = true;
                    }
                    ClauseState::Unresolved => {}
                }
            }
        }

        None
    }

    fn backtrack(&mut self, target_level: usize) {
        debug!(
            "backtrack: level {} -> {}",
            self.decision_level, target_level
        );
        let cut = self.trail_lim[target_level];

        for assignment in self.trail.drain(cut..) {
            trace!(
                "unassign {}@L{}",
                Self::lit_to_string(assignment.lit),
                assignment.level
            );
            self.assignments[assignment.var()] = None;
        }

        self.trail_lim.truncate(target_level + 1);
        self.decision_level = target_level;
    }

    fn analyze_conflict(&self, id: ClauseId) -> (Clause, usize) {
        let mut learned: HashSet<Lit> = HashSet::from_iter(self.clauses[id].clone());
        debug!(
            "analyze_conflict: cid={}, level={}, initial_clause=({})",
            id,
            self.decision_level,
            Self::clause_to_string(&self.clauses[id])
        );
        let start = *self.trail_lim.last().unwrap();
        let current_assignments = &mut self.trail[start..].iter().rev();

        for assignment in current_assignments {
            let num_current = learned
                .iter()
                .filter(|&l| self.assignments[l.var].as_ref().unwrap().level == self.decision_level)
                .count();
            trace!(
                "first-UIP loop: var={}, current_level_lits={}",
                assignment.var(),
                num_current
            );

            if num_current == 1 {
                let uip = learned
                    .iter()
                    .find(|lit| self.assignments[lit.var].as_ref().unwrap().level == self.decision_level)
                    .copied();
                if let Some(uip) = uip {
                    debug!("first-UIP found at {}", Self::lit_to_string(uip));
                } else {
                    debug!("first-UIP found (no current-level literal resolved)");
                }
                break;
            }
            let pivot = assignment.var();

            if !learned.contains(&Lit::pos(pivot)) && !learned.contains(&Lit::neg(pivot)) {
                trace!("skip pivot x{}: not in learned clause", pivot + 1);
                continue;
            }

            let Reason::Deduced(cid) = assignment.reason else {
                trace!(
                    "skip pivot x{}: assignment is a decision literal",
                    pivot + 1
                );
                continue;
            };

            debug!(
                "resolve on x{} using reason c{}: ({})",
                pivot + 1,
                cid,
                Self::clause_to_string(&self.clauses[cid])
            );
            learned.extend(&self.clauses[cid]);
            learned.remove(&Lit::pos(pivot));
            learned.remove(&Lit::neg(pivot));
            debug!("learned now: ({})", Self::learned_to_string(&learned));
        }

        let mut backjump_level = 0;

        for &lit in &learned {
            let level = self.assignments[lit.var].as_ref().unwrap().level;
            if level != self.decision_level {
                backjump_level = backjump_level.max(level);
            }
        }

        debug!(
            "learned final: ({}) ; backjump_level={}",
            Self::learned_to_string(&learned),
            backjump_level
        );

        (learned.into_iter().collect(), backjump_level)
    }

    fn pick_branch_lit(&self) -> Option<Lit> {
        let var = (0..self.num_vars).find(|&v| self.assignments[v].is_none())?;
        Some(Lit { var, val: true })
    }

    fn assign(&mut self, lit: Lit, reason: Reason) {
        debug_assert!(self.assignments[lit.var].is_none());
        match &reason {
            Reason::Decided => {
                debug!(
                    "assign decision {} at level {}",
                    Self::lit_to_string(lit),
                    self.decision_level
                );
            }
            Reason::Deduced(cid) => {
                debug!(
                    "assign implied {} at level {} from c{}: ({})",
                    Self::lit_to_string(lit),
                    self.decision_level,
                    cid,
                    Self::clause_to_string(&self.clauses[*cid])
                );
            }
        }
        let assignment = Assignment {
            lit,
            level: self.decision_level,
            reason,
        };
        self.assignments[lit.var] = Some(assignment.clone());
        self.trail.push(assignment);
    }

    pub fn solve(&mut self) -> bool {
        loop {
            trace!(
                "solve loop: level={}, trail_len={}, clauses={}",
                self.decision_level,
                self.trail.len(),
                self.clauses.len()
            );
            if let Some(conflict_cid) = self.propagate() {
                if self.decision_level == 0 {
                    debug!("unsat at root level due to conflict c{}", conflict_cid);
                    return false;
                }

                let (learned, backjump_level) = self.analyze_conflict(conflict_cid);
                debug!(
                    "append learned clause c{}: ({})",
                    self.clauses.len(),
                    Self::clause_to_string(&learned)
                );

                self.clauses.push(learned.clone());

                self.backtrack(backjump_level);
            } else {
                let Some(lit) = self.pick_branch_lit() else {
                    debug!("satisfiable: all variables assigned without conflict");
                    return true;
                };
                self.decision_level += 1;
                self.trail_lim.push(self.trail.len());
                self.assign(lit, Reason::Decided)
            }
        }
    }
}
