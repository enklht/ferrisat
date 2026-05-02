use ferrisat::Solver;
use ferrisat::cnf::parse_dimacs_cnf;
use std::{env, fs, process};

fn main() {
    let path = env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: program <file>");
        process::exit(1);
    });

    println!("loading from {}...", path);
    let contents = fs::read_to_string(&path).unwrap_or_else(|err| {
        eprintln!("failed to read {}: {}", path, err);
        process::exit(1);
    });

    let formula = parse_dimacs_cnf(&contents).unwrap_or_else(|err| {
        eprintln!("failed to parse {}: {}", path, err);
        process::exit(1);
    });

    println!("num_vars:    {}", formula.num_vars);
    println!("num_clauses: {}", formula.clauses.len());
    let mut solver = Solver::new(formula.num_vars, formula.clauses);
    println!("{}", solver.solve());
}
