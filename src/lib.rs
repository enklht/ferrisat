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

fn resolve(c1: &Clause, c2: &Clause, pivot: usize) -> Clause {
    let mut resolved = Vec::new();

    for &lit in c1 {
        if lit.var != pivot {
            resolved.push(lit)
        }
    }

    for &lit in c2 {
        if lit.var != pivot && !resolved.contains(&lit) {
            resolved.push(lit)
        }
    }

    resolved
}

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
    clauses: Vec<Clause>,
    assignments: Vec<Option<Assignment>>,
    trail: Vec<Assignment>,
    trail_lim: Vec<usize>,
    decision_level: usize,
    num_vars: usize,
}

impl Solver {
    pub fn new(num_vars: usize, clauses: Vec<Clause>) -> Self {
        Solver {
            clauses,
            assignments: vec![None; num_vars],
            trail: Vec::new(),
            trail_lim: vec![0],
            decision_level: 0,
            num_vars,
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

    fn backtrack(&mut self, target_level: usize) {
        let cut = self.trail_lim[target_level];

        for assignment in self.trail.drain(cut..) {
            self.assignments[assignment.var()] = None;
        }

        self.trail_lim.truncate(target_level + 1);
        self.decision_level = target_level;
    }

    fn analyze_conflict(&self, id: ClauseId) -> (Clause, usize) {
        let mut learned = self.clauses[id].clone();
        let start = *self.trail_lim.last().unwrap();
        let current_assignments = &mut self.trail[start..].iter().rev();

        let mut seen = vec![false; self.num_vars];
        let mut num_current = 0;

        for lit in &learned {
            if !seen[lit.var] {
                seen[lit.var] = true;

                let assignment = self.assignments[lit.var].as_ref().unwrap();
                if assignment.level == self.decision_level {
                    num_current += 1;
                }
            }
        }

        while num_current > 1 {
            let Some(assignment) = current_assignments.next() else {
                break;
            };
            let pivot = assignment.var();

            if !seen[pivot] {
                continue;
            }

            let Reason::Deduced(cid) = assignment.reason else {
                continue;
            };

            learned = resolve(&learned, &self.clauses[cid], pivot);

            seen.fill(false);
            num_current = 0;

            for lit in &learned {
                if !seen[lit.var] {
                    seen[lit.var] = true;

                    let assignment = self.assignments[lit.var].as_ref().unwrap();
                    if assignment.level == self.decision_level {
                        num_current += 1;
                    }
                }
            }
        }

        let mut backjump_level = 0;

        for &lit in &learned {
            let level = self.assignments[lit.var].as_ref().unwrap().level;
            if level != self.decision_level {
                backjump_level = backjump_level.max(level);
            }
        }

        (learned, backjump_level)
    }

    fn pick_branch_lit(&self) -> Option<Lit> {
        let var = (0..self.num_vars).find(|&v| self.assignments[v].is_none())?;
        Some(Lit { var, val: true })
    }

    fn assign(&mut self, lit: Lit, reason: Reason) {
        debug_assert!(self.assignments[lit.var].is_none());
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
            if let Some(conflict_cid) = self.propagate() {
                if self.decision_level == 0 {
                    return false;
                }

                let (learned, backjump_level) = self.analyze_conflict(conflict_cid);

                self.clauses.push(learned.clone());

                self.backtrack(backjump_level);
            } else {
                let Some(lit) = self.pick_branch_lit() else {
                    return true;
                };
                self.decision_level += 1;
                self.trail_lim.push(self.trail.len());
                self.assign(lit, Reason::Decided)
            }
        }
    }
}
