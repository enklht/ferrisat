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

    pub fn reducible(
        &self,
        lit: Lit,
        var_data: &VarData,
        clause_data: &ClauseData,
        memo: &mut Vec<Option<bool>>,
    ) -> bool {
        match memo[lit.var()] {
            Some(b) => b,
            None => {
                let reason = &var_data.assignment_of(lit.var()).reason;
                match reason {
                    &Reason::Deduced(cid) => {
                        assert!(!clause_data.deleted(cid));
                        let reducible = clause_data.get(cid).iter().all(|&l| {
                            l == lit.negated()
                                || self.contains(l.var())
                                || self.reducible(l, var_data, clause_data, memo)
                        });
                        memo[lit.var()] = Some(reducible);
                        reducible
                    }
                    _ => {
                        memo[lit.var()] = Some(false);
                        false
                    }
                }
            }
        }
    }

    pub fn simplify(&mut self, var_data: &VarData, clause_data: &ClauseData) {
        for &lit in &self.candidates {
            let memo = &mut vec![None; var_data.num_vars()];

            if self.seen[lit.var()] && self.reducible(lit, var_data, clause_data, memo) {
                self.seen[lit.var()] = false;
            }
        }
    }
}
