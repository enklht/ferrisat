use ferrisat::Solver;
use ferrisat::cnf::parse_dimacs_cnf;
use std::fs;
use std::path::PathBuf;

fn construct_solver(path: String) -> Solver {
    let full_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(&path);
    let content =
        fs::read_to_string(&full_path).unwrap_or_else(|e| panic!("failed to read {}: {}", path, e));

    let formula =
        parse_dimacs_cnf(&content).unwrap_or_else(|e| panic!("failed to parse {}: {}", path, e));
    assert!(formula.num_vars > 0, "unexpected num_vars in {}", path);
    assert!(
        !formula.clauses.is_empty(),
        "unexpected empty clauses in {}",
        path
    );

    formula.into_solver()
}

fn main() {
    let path = "data/uuf250-1065/uuf250-01.cnf".to_string();
    let mut solver = construct_solver(path);
    assert!(!solver.solve());
}
