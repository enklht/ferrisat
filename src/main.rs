use cdcl_rs::cnf::parse_dimacs_cnf;
use std::{env, fs, process};

fn main() {
    let path = env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: program <file>");
        process::exit(1);
    });

    let contents = fs::read_to_string(&path).unwrap_or_else(|err| {
        eprintln!("failed to read {}: {}", path, err);
        process::exit(1);
    });

    let solver = parse_dimacs_cnf(&contents).unwrap_or_else(|err| {
        eprintln!("failed to parse {}: {}", path, err);
        process::exit(1);
    });

    println!("{}", solver.into_solver().solve());
}
