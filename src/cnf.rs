use crate::{Clause, Lit};

#[derive(Debug, Clone, PartialEq, Eq)]
enum SubsumptionResult {
    Keep,
    RemoveClause,
    RemoveLitAt(usize),
}

fn subsumes(c: &Clause, d: &Clause) -> SubsumptionResult {
    if d.len() < c.len() {
        return SubsumptionResult::Keep;
    }

    let mut candidate = None;
    'outer: for &ci in c {
        for (i, &di) in d.iter().enumerate() {
            if ci == di {
                continue 'outer;
            } else if ci == di.negated() {
                if candidate.is_some() {
                    return SubsumptionResult::Keep;
                }
                candidate = Some(i);
                continue 'outer;
            }
        }

        return SubsumptionResult::Keep;
    }

    match candidate {
        Some(i) => SubsumptionResult::RemoveLitAt(i),
        None => SubsumptionResult::RemoveClause,
    }
}

fn resolve(c: &Clause, d: &Clause, v: usize) -> Option<Clause> {
    let mut resolvent = Vec::new();

    for &lit in c {
        if lit.var() != v {
            resolvent.push(lit);
        }
    }
    for &lit in d {
        if lit.var() != v {
            resolvent.push(lit);
        }
    }

    resolvent.sort();
    resolvent.dedup();

    if resolvent
        .windows(2)
        .find(|&window| window[0] == window[1].negated())
        .is_none()
    {
        Some(resolvent)
    } else {
        None
    }
}

#[derive(Debug, Clone)]
pub struct CNF {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

impl CNF {
    pub fn simplify(&mut self) {
        for mut clause in std::mem::take(&mut self.clauses) {
            clause.sort();
            clause.dedup();

            if clause
                .windows(2)
                .find(|&window| window[0] == window[1].negated())
                .is_none()
            {
                self.clauses.push(clause);
            }
        }

        self.backward_subsumption_fixpoint();
        self.eliminate_all();
        self.backward_subsumption_fixpoint();
    }

    fn backward_subsumption_fixpoint(&mut self) {
        while self.backward_subsumption_step() {}
    }

    fn backward_subsumption_step(&mut self) -> bool {
        let mut changed = false;
        let clauses = std::mem::take(&mut self.clauses);
        let mut pending_operations = vec![SubsumptionResult::Keep; clauses.len()];

        let mut occurs = vec![Vec::new(); self.num_vars];
        for (cid, clause) in clauses.iter().enumerate() {
            for &lit in clause {
                occurs[lit.var()].push(cid);
            }
        }

        for cid in 0..clauses.len() {
            let pivot = clauses[cid]
                .iter()
                .min_by_key(|lit| occurs[lit.var()].len())
                .unwrap();
            for &did in &occurs[pivot.var()] {
                if cid == did
                    || pending_operations[cid] != SubsumptionResult::Keep
                    || pending_operations[did] == SubsumptionResult::RemoveClause
                {
                    continue;
                }
                match subsumes(&clauses[cid], &clauses[did]) {
                    SubsumptionResult::Keep => {}
                    other => {
                        pending_operations[did] = other;
                    }
                }
            }
        }

        for (cid, mut clause) in clauses.into_iter().enumerate() {
            match pending_operations[cid] {
                SubsumptionResult::Keep => {
                    self.clauses.push(clause);
                }
                SubsumptionResult::RemoveClause => {
                    changed = true;
                }
                SubsumptionResult::RemoveLitAt(i) => {
                    clause.swap_remove(i);
                    self.clauses.push(clause);
                    changed = true;
                }
            }
        }

        changed
    }

    fn eliminate_all(&mut self) {
        for v in 0..self.num_vars {
            let clauses = std::mem::take(&mut self.clauses);

            let mut contains_pos = Vec::new();
            let mut contains_neg = Vec::new();
            let mut others = Vec::new();

            for (cid, clause) in clauses.iter().enumerate() {
                if clause.contains(&Lit::pos(v)) {
                    contains_pos.push(cid)
                } else if clause.contains(&Lit::neg(v)) {
                    contains_neg.push(cid)
                } else {
                    others.push(cid)
                }
            }

            let mut resolvents = Vec::new();

            for &cid in &contains_pos {
                for &did in &contains_neg {
                    if let Some(clause) = resolve(&clauses[cid], &clauses[did], v) {
                        resolvents.push(clause);
                    }
                }
            }

            if resolvents.len() < contains_pos.len() + contains_neg.len() {
                for cid in others {
                    self.clauses.push(clauses[cid].clone());
                }
                for clause in resolvents {
                    self.clauses.push(clause);
                }
            } else {
                self.clauses = clauses;
            }
        }
    }

    pub fn from_dimacs(input: &str) -> Result<CNF, String> {
        let mut num_vars = None;
        let mut expected_clauses = None;
        let mut clauses = Vec::new();
        let mut current_clause: Vec<Lit> = Vec::new();

        for (line_no, raw_line) in input.lines().enumerate() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('c') {
                continue;
            }
            if line.starts_with('%') {
                break;
            }

            if line.starts_with('p') {
                let parts: Vec<_> = line.split_whitespace().collect();
                if parts.len() != 4 || parts[0] != "p" || parts[1] != "cnf" {
                    return Err(format!("invalid header at line {}", line_no + 1));
                }

                let vars = parts[2]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid variable count at line {}", line_no + 1))?;
                let cls = parts[3]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid clause count at line {}", line_no + 1))?;

                num_vars = Some(vars);
                expected_clauses = Some(cls);
                continue;
            }

            for token in line.split_whitespace() {
                let lit = token
                    .parse::<isize>()
                    .map_err(|_| format!("invalid literal '{}' at line {}", token, line_no + 1))?;

                if lit == 0 {
                    if current_clause.is_empty() {
                        return Err(format!("empty clause at line {}", line_no + 1));
                    }
                    clauses.push(std::mem::take(&mut current_clause));
                    continue;
                }

                let var = lit.unsigned_abs();
                if var == 0 {
                    return Err(format!("invalid variable id at line {}", line_no + 1));
                }
                if let Some(limit) = num_vars
                    && var > limit
                {
                    return Err(format!("variable {} exceeds declared bound {}", var, limit));
                }

                let lit = if lit > 0 {
                    Lit::pos(var - 1)
                } else {
                    Lit::neg(var - 1)
                };
                current_clause.push(lit);
            }
        }

        if !current_clause.is_empty() {
            return Err("last clause must be terminated with 0".to_string());
        }

        let num_vars = num_vars.ok_or_else(|| "missing DIMACS header".to_string())?;

        if let Some(expected) = expected_clauses
            && clauses.len() != expected
        {
            return Err(format!(
                "clause count mismatch: expected {}, got {}",
                expected,
                clauses.len()
            ));
        }

        Ok(CNF { num_vars, clauses })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_simple_dimacs() {
        let input = "c example\np cnf 3 2\n1 -2 0\n3 0\n";
        let parsed = CNF::from_dimacs(input).unwrap();

        assert_eq!(parsed.num_vars, 3);
        assert_eq!(parsed.clauses.len(), 2);
    }

    #[test]
    fn rejects_unterminated_clause() {
        let input = "p cnf 2 1\n1 -2\n";
        assert!(CNF::from_dimacs(input).is_err());
    }
}
