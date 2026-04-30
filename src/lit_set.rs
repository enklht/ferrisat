use super::*;
pub(crate) struct LitSet {
    candidates: Vec<Lit>,
    seen: Vec<bool>,
    pub num_current_level: usize,
}

impl LitSet {
    pub fn new(clause: &Clause, solver: &Solver) -> LitSet {
        let mut litset = LitSet {
            candidates: vec![],
            seen: vec![false; solver.num_vars],
            num_current_level: 0,
        };

        litset.extend(clause, solver);

        litset
    }

    pub fn contains(&self, lit: Lit) -> bool {
        self.seen[lit.var]
    }

    pub fn extend(&mut self, clause: &Clause, solver: &Solver) {
        for &lit in clause {
            let assignment = solver.assignment_of(lit);
            if !self.seen[lit.var] && assignment.level == solver.decision_level {
                self.num_current_level += 1;
            }
            self.seen[lit.var] = true;
            self.candidates.push(lit);
        }
    }

    pub fn remove(&mut self, lit: Lit, solver: &Solver) {
        let assignment = solver.assignment_of(lit);
        if self.seen[lit.var] && assignment.level == solver.decision_level {
            self.num_current_level -= 1;
        }
        self.seen[lit.var] = false;
    }

    pub fn simplify(&mut self, solver: &Solver) {
        self.candidates.sort_unstable();
        self.candidates.dedup();

        for &lit in &self.candidates {
            if self.seen[lit.var] {
                let assignment = solver.assignment_of(lit);

                if assignment.level == solver.decision_level {
                    continue;
                }

                let Reason::Deduced(cid) = assignment.reason else {
                    continue;
                };

                if solver.clauses[cid]
                    .iter()
                    .all(|l| self.seen[l.var] || lit == l.negated())
                {
                    self.seen[lit.var] = false;
                }
            }
        }
    }

    pub fn into_analysis_result(self, solver: &Solver) -> (Vec<Lit>, u16, Lit, usize) {
        let mut clause = Vec::new();
        let mut asserted_lit = Lit::pos(0); // placeholder to be overwritten
        let mut backjump_level = 0;
        let mut seen_levels = vec![false; solver.decision_level + 1];

        for &lit in &self.candidates {
            if self.seen[lit.var] {
                let level = solver.assignment_of(lit).level;

                if level == solver.decision_level {
                    asserted_lit = lit;
                } else {
                    backjump_level = backjump_level.max(level);
                }

                seen_levels[level] = true;

                clause.push(lit);

                // deduplication
                // self.seen[lit.var] = false;
            }
        }

        let lbd = seen_levels.iter().filter(|&seen| *seen).count() as u16;
        (clause, lbd, asserted_lit, backjump_level)
    }
}
