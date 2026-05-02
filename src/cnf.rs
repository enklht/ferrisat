use crate::{Lit, Solver};

#[derive(Debug, Clone)]
pub struct CnfFormula {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

pub fn parse_dimacs_cnf(input: &str) -> Result<CnfFormula, String> {
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

    let vars = num_vars.ok_or_else(|| "missing DIMACS header".to_string())?;

    if let Some(expected) = expected_clauses
        && clauses.len() != expected
    {
        return Err(format!(
            "clause count mismatch: expected {}, got {}",
            expected,
            clauses.len()
        ));
    }

    Ok(CnfFormula {
        num_vars: vars,
        clauses,
    })
}

#[cfg(test)]
mod tests {
    use super::parse_dimacs_cnf;

    #[test]
    fn parses_simple_dimacs() {
        let input = "c example\np cnf 3 2\n1 -2 0\n3 0\n";
        let parsed = parse_dimacs_cnf(input).unwrap();

        assert_eq!(parsed.num_vars, 3);
        assert_eq!(parsed.clauses.len(), 2);
    }

    #[test]
    fn rejects_unterminated_clause() {
        let input = "p cnf 2 1\n1 -2\n";
        assert!(parse_dimacs_cnf(input).is_err());
    }
}
