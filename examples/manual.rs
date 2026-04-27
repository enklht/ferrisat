use cdcl_rs::*;

fn main() {
    let pos = Lit::pos;
    let neg = Lit::neg;

    let clauses = vec![
        vec![neg(1), neg(2)],
        vec![neg(1), pos(3)],
        vec![neg(3), neg(4)],
        vec![pos(2), pos(4), pos(5)],
        vec![neg(5), pos(6), neg(7)],
        vec![pos(2), pos(7), pos(8)],
        vec![neg(8), neg(9)],
        vec![pos(9), neg(10), pos(11)],
        vec![neg(10), neg(12)],
        vec![neg(11), pos(12)],
    ];

    let mut solver = Solver::new(13, clauses);
    let sat = solver.solve();

    println!("SAT = {}", sat);
}
