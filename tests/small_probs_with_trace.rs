use cdcl_rs::{Lit, Solver};
use log::info;
use std::sync::Once;

static LOGGER: Once = Once::new();

fn init_logger() {
    LOGGER.call_once(|| {
        let mut builder = env_logger::Builder::from_default_env();
        builder.is_test(true).try_init().ok();
    });
}

#[test]
fn small_sat_trace() {
    init_logger();

    // SAT example that still shows implication flow:
    // (x1 v x2) ^ (~x1 v x2)
    // With the current branching policy, deciding x1=true implies x2=true.
    let clauses = vec![
        vec![Lit::pos(0), Lit::pos(1)],
        vec![Lit::neg(0), Lit::pos(1)],
    ];

    info!("running toy SAT trace test with {} clauses", clauses.len());

    let mut solver = Solver::new(2, clauses);
    assert!(solver.solve());
}

#[test]
fn small_unsat_trace() {
    init_logger();

    // Unsat 2-SAT core with no root-level unit clauses:
    // (x1 v x2) ^ (x1 v ~x2) ^ (~x1 v x2) ^ (~x1 v ~x2)
    // This forces a conflict after a decision and triggers conflict analysis.
    let clauses = vec![
        vec![Lit::pos(0), Lit::pos(1)],
        vec![Lit::pos(0), Lit::neg(1)],
        vec![Lit::neg(0), Lit::pos(1)],
        vec![Lit::neg(0), Lit::neg(1)],
    ];

    info!("running toy first-UIP test with {} clauses", clauses.len());

    let mut solver = Solver::new(2, clauses);
    assert!(!solver.solve());
}
