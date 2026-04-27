use cdcl_rs::Solver;
use cdcl_rs::cnf::parse_dimacs_cnf;
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

#[test]
fn uf20_91() {
    for i in 1..=1000 {
        let path = format!("data/uf20-91/uf20-0{i}.cnf");
        let mut solver = construct_solver(path);
        assert!(solver.solve());
    }
}

#[test]
fn uf75_325() {
    for i in 1..=100 {
        let path = format!("data/uf75-325/uf75-0{i}.cnf");
        let mut solver = construct_solver(path);
        assert!(solver.solve());
    }
}

#[test]
fn uuf75_325() {
    for i in 1..=100 {
        let path = format!("data/uuf75-325/uuf75-0{i}.cnf");
        let mut solver = construct_solver(path);
        assert!(!solver.solve());
    }
}

// #[test]
// fn uf250_1065() {
//     for i in 1..=1 {
//         let path = format!("data/uf250-1065/uf250-0{i}.cnf");
//         let mut solver = construct_solver(path);
//         assert!(!solver.solve());
//     }
// }
