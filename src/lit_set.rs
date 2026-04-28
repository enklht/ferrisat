use super::*;

pub(crate) struct LitSet {
    num_vars: usize,
    candidates: Vec<Lit>,
    seen: Vec<bool>,
    pub num_current_level: usize,
}

impl LitSet {
    // considering that conflicting clause will never have both pos and neg,
    // seen can be a vec of size num_vars and we dont need indices
    pub fn new(clause: &Clause, solver: &Solver) -> LitSet {
        let mut litset = LitSet {
            num_vars: solver.num_vars,
            candidates: vec![],
            seen: vec![false; 2 * solver.num_vars],
            num_current_level: 0,
        };

        litset.extend(clause, solver);

        litset
    }

    fn get_index(&self, lit: &Lit) -> usize {
        if lit.val {
            lit.var + self.num_vars
        } else {
            lit.var
        }
    }

    pub fn contains(&self, lit: &Lit) -> bool {
        if lit.val {
            self.seen[lit.var + self.num_vars]
        } else {
            self.seen[lit.var]
        }
    }

    pub fn extend(&mut self, clause: &Clause, solver: &Solver) {
        for lit in clause {
            let index = self.get_index(lit);

            if !self.seen[self.get_index(lit)]
                && solver.assignments[lit.var].as_ref().unwrap().level == solver.decision_level
            {
                self.num_current_level += 1;
            }
            self.seen[index] = true;
            self.candidates.push(*lit);
        }
    }

    pub fn remove(&mut self, lit: &Lit, solver: &Solver) {
        let index = self.get_index(lit);

        if self.seen[self.get_index(lit)]
            && solver.assignments[lit.var].as_ref().unwrap().level == solver.decision_level
        {
            self.num_current_level -= 1;
        }
        self.seen[index] = false;
    }

    pub fn simplify(&mut self, solver: &Solver) {
        for lit in &self.candidates {
            let index = self.get_index(lit);
            if self.seen[self.get_index(lit)] {
                let assignment = solver.assignments[lit.var].as_ref().unwrap();

                if assignment.level == solver.decision_level {
                    continue;
                }

                if let Reason::Deduced(cid) = assignment.reason
                    && solver.clauses[cid]
                        .iter()
                        .all(|l| self.seen[self.get_index(l)] || *lit == l.negated())
                {
                    self.seen[index] = false;
                }
            }
        }
    }

    pub fn into_analysis_result(self, solver: &Solver) -> (Clause, Lit, usize) {
        let mut clause = Vec::new();
        let mut asserted_lit = Lit::pos(0); // placeholder to be overwritten
        let mut backjump_level = 0;

        for lit in &self.candidates {
            let index = self.get_index(lit);
            if self.seen[index] {
                let level = solver.assignments[lit.var].as_ref().unwrap().level;

                if level == solver.decision_level {
                    asserted_lit = *lit;
                } else {
                    backjump_level = backjump_level.max(level);
                }

                clause.push(*lit);
            }
        }

        (clause, asserted_lit, backjump_level)
    }
}
