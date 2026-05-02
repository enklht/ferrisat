use super::*;
pub(crate) struct LitSet {
    pub candidates: Vec<Lit>,
    pub seen: Vec<bool>,
}

impl LitSet {
    pub fn new(num_vars: usize) -> LitSet {
        LitSet {
            candidates: vec![],
            seen: vec![false; num_vars],
        }
    }

    pub fn contains(&self, var: usize) -> bool {
        self.seen[var]
    }

    pub fn push(&mut self, lit: Lit) -> bool {
        if self.seen[lit.var()] {
            return false;
        }

        self.seen[lit.var()] = true;
        self.candidates.push(lit);
        true
    }

    pub fn remove(&mut self, var: usize) -> bool {
        if !self.seen[var] {
            return false;
        }

        self.seen[var] = false;
        true
    }

    pub fn into_vec(self) -> Clause {
        let mut clause = Vec::new();
        for lit in self.candidates {
            if self.seen[lit.var()] {
                clause.push(lit)
            }
        }
        clause
    }
    //
    // pub fn simplify(&mut self, var_data: &VarData, clauses: &[Clause]) {
    //     for &lit in &self.candidates {
    //         if self.seen[lit.var()] {
    //             let assignment = var_data.assignment_of(lit.var());
    //
    //             if assignment.level == self.decision_level {
    //                 continue;
    //             }
    //
    //             let Reason::Deduced(cid) = assignment.reason else {
    //                 continue;
    //             };
    //
    //             if clauses[cid]
    //                 .iter()
    //                 .all(|l| self.seen[l.var()] || lit == l.negated())
    //             {
    //                 self.seen[lit.var()] = false;
    //             }
    //         }
    //     }
    // }
}
