use super::*;
pub(crate) struct LitSet {
    candidates: Vec<Lit>,
    seen: Vec<bool>,
    pub num_current_level: usize,
    decision_level: usize,
}

impl LitSet {
    pub fn new(clause: &Clause, solver: &Solver) -> LitSet {
        let mut litset = LitSet {
            candidates: vec![],
            seen: vec![false; solver.num_vars],
            num_current_level: 0,
            decision_level: solver.decision_level,
        };

        litset.extend(clause, &solver.var_data);

        litset
    }

    pub fn contains(&self, var: usize) -> bool {
        self.seen[var]
    }

    pub fn extend(&mut self, clause: &Clause, var_data: &VarData) {
        for &lit in clause {
            if self.seen[lit.var()] {
                continue;
            }

            self.seen[lit.var()] = true;
            self.candidates.push(lit);

            let assignment = var_data.assignment_of(lit.var());
            if assignment.level == self.decision_level {
                self.num_current_level += 1;
            }
        }
    }

    pub fn remove(&mut self, lit: Lit, var_data: &VarData) {
        let var = lit.var();
        let assignment = var_data.assignment_of(var);
        if self.seen[var] && assignment.level == self.decision_level {
            self.num_current_level -= 1;
        }
        self.seen[lit.var()] = false;
    }

    pub fn simplify(&mut self, var_data: &VarData, clauses: &[Clause]) {
        for &lit in &self.candidates {
            if self.seen[lit.var()] {
                let assignment = var_data.assignment_of(lit.var());

                if assignment.level == self.decision_level {
                    continue;
                }

                let Reason::Deduced(cid) = assignment.reason else {
                    continue;
                };

                if clauses[cid]
                    .iter()
                    .all(|l| self.seen[l.var()] || lit == l.negated())
                {
                    self.seen[lit.var()] = false;
                }
            }
        }
    }

    pub fn into_analysis_result(self, var_data: &VarData) -> (Vec<Lit>, u16, Lit, usize) {
        let mut clause = Vec::new();
        let mut asserted_lit = Lit::pos(0); // placeholder to be overwritten
        let mut backjump_level = 0;
        let mut seen_levels = vec![false; self.decision_level + 1];

        for &lit in &self.candidates {
            let var = lit.var();

            if self.seen[var] {
                let level = var_data.assignment_of(var).level;

                if level == self.decision_level {
                    asserted_lit = lit;
                } else {
                    backjump_level = backjump_level.max(level);
                }

                seen_levels[level] = true;

                clause.push(lit);
            }
        }

        let lbd = seen_levels.iter().filter(|&seen| *seen).count() as u16;
        (clause, lbd, asserted_lit, backjump_level)
    }
}
