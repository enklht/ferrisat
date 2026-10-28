use ferrisat::{CNF, Clause, Lit, Solver};

fn assert_solves(num_vars: usize, clauses: Vec<Clause>, expected: bool) {
    for simplify in [false, true] {
        let mut formula = CNF {
            num_vars,
            clauses: clauses.clone(),
        };
        if simplify {
            formula.simplify();
        }
        let mut solver = Solver::new(num_vars, formula.clauses);
        assert_eq!(solver.solve(), expected, "simplify={simplify}: {clauses:?}");
        if expected {
            assert!(clauses.iter().all(|clause| {
                clause
                    .iter()
                    .any(|lit| solver.value_of(lit.var()) == Some(lit.val()))
            }));
        }
        assert_eq!(solver.solve(), expected, "repeated solve: {clauses:?}");
    }
}

#[test]
fn opposite_units_are_unsatisfiable() {
    for first in [Lit::pos(0), Lit::neg(0)] {
        assert_solves(1, vec![vec![first], vec![first.negated()]], false);
    }
}

#[test]
fn duplicate_units_are_satisfiable() {
    for lit in [Lit::pos(0), Lit::neg(0)] {
        assert_solves(1, vec![vec![lit], vec![lit]], true);
    }
}

#[test]
fn empty_clause_is_unsatisfiable() {
    assert_solves(0, vec![vec![]], false);
    assert_solves(1, vec![vec![Lit::pos(0)], vec![]], false);
}

#[test]
fn root_conflict_remains_unsatisfiable_on_repeat() {
    let mut solver = Solver::new(
        2,
        vec![
            vec![Lit::pos(0)],
            vec![Lit::neg(0), Lit::pos(1)],
            vec![Lit::neg(0), Lit::neg(1)],
        ],
    );
    assert!(!solver.solve());
    assert!(!solver.solve());
}

#[test]
fn empty_formula_is_satisfiable() {
    assert_solves(0, vec![], true);
    assert_solves(3, vec![], true);
}

#[test]
fn unit_propagation_preserves_the_model() {
    assert_solves(
        3,
        vec![
            vec![Lit::pos(0)],
            vec![Lit::neg(0), Lit::pos(1)],
            vec![Lit::neg(1), Lit::neg(2)],
        ],
        true,
    );
}

#[test]
fn unit_propagation_detects_a_contradiction() {
    assert_solves(
        2,
        vec![
            vec![Lit::pos(0)],
            vec![Lit::neg(0), Lit::pos(1)],
            vec![Lit::neg(1)],
        ],
        false,
    );
}

#[test]
fn binary_clause_contradiction_survives_simplification() {
    assert_solves(
        2,
        vec![
            vec![Lit::pos(0), Lit::pos(1)],
            vec![Lit::pos(0), Lit::neg(1)],
            vec![Lit::neg(0), Lit::pos(1)],
            vec![Lit::neg(0), Lit::neg(1)],
        ],
        false,
    );
}

#[test]
fn command_line_reports_contradictions_without_panicking() {
    let path =
        std::env::temp_dir().join(format!("ferrisat-contradiction-{}.cnf", std::process::id()));
    std::fs::write(&path, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrisat"))
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(path).unwrap();

    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty(), "{:?}", output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().lines().last(),
        Some("false")
    );
}

fn brute_force(num_vars: usize, clauses: &[Clause]) -> bool {
    (0..1usize << num_vars).any(|mask| {
        clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|lit| ((mask >> lit.var()) & 1 == 1) == lit.val())
        })
    })
}

#[test]
fn all_two_variable_formulas_match_brute_force() {
    let possible_clauses: Vec<Clause> = (0..9)
        .map(|mut code| {
            let mut clause = Vec::new();
            for var in 0..2 {
                match code % 3 {
                    1 => clause.push(Lit::pos(var)),
                    2 => clause.push(Lit::neg(var)),
                    _ => {}
                }
                code /= 3;
            }
            clause
        })
        .collect();

    for subset in 0..1usize << possible_clauses.len() {
        let clauses: Vec<Clause> = possible_clauses
            .iter()
            .enumerate()
            .filter(|(i, _)| subset & (1 << i) != 0)
            .map(|(_, clause)| clause.clone())
            .collect();
        let expected = brute_force(2, &clauses);
        assert_solves(2, clauses, expected);
    }
}

#[test]
fn generated_formulas_match_brute_force() {
    fn next(seed: &mut u64, limit: usize) -> usize {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        (*seed as usize) % limit
    }

    let mut seed = 0x7f4a7c159e3779b9;
    for _ in 0..2_000 {
        let num_vars = 3 + next(&mut seed, 7);
        let num_clauses = 1 + next(&mut seed, 6 * num_vars);
        let mut clauses = Vec::new();
        for _ in 0..num_clauses {
            let len = 2 + next(&mut seed, num_vars.min(5) - 1);
            let mut clause: Clause = Vec::new();
            while clause.len() < len {
                let var = next(&mut seed, num_vars);
                let val = next(&mut seed, 2) == 0;
                if !clause.iter().any(|lit| lit.var() == var) {
                    clause.push(Lit::new(var, val));
                }
            }
            clauses.push(clause);
        }
        let expected = brute_force(num_vars, &clauses);
        assert_solves(num_vars, clauses, expected);
    }
}
