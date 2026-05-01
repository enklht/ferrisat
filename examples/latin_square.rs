use cdcl_rs::*;

fn var_index(row: usize, col: usize, symbol: usize, size: usize) -> usize {
    (row * size + col) * size + symbol
}

fn add_exactly_one(clauses: &mut Vec<Vec<Lit>>, vars: &[usize]) {
    let pos = Lit::pos;
    let neg = Lit::neg;

    let mut clause = Vec::with_capacity(vars.len());
    for &var in vars {
        clause.push(pos(var));
    }
    clauses.push(clause);

    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            clauses.push(vec![neg(vars[i]), neg(vars[j])]);
        }
    }
}

#[allow(unused_variables)]
fn main() {
    let pos = Lit::pos;
    let neg = Lit::neg;

    const SIZE: usize = 4;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    // Each cell has exactly one symbol.
    for row in 0..SIZE {
        for col in 0..SIZE {
            let mut vars = Vec::with_capacity(SIZE);
            for symbol in 0..SIZE {
                vars.push(var_index(row, col, symbol, SIZE));
            }
            add_exactly_one(&mut clauses, &vars);
        }
    }

    // Each row has each symbol exactly once.
    for row in 0..SIZE {
        for symbol in 0..SIZE {
            let mut vars = Vec::with_capacity(SIZE);
            for col in 0..SIZE {
                vars.push(var_index(row, col, symbol, SIZE));
            }
            add_exactly_one(&mut clauses, &vars);
        }
    }

    // Each column has each symbol exactly once.
    for col in 0..SIZE {
        for symbol in 0..SIZE {
            let mut vars = Vec::with_capacity(SIZE);
            for row in 0..SIZE {
                vars.push(var_index(row, col, symbol, SIZE));
            }
            add_exactly_one(&mut clauses, &vars);
        }
    }

    // Symmetry breaking: fix first row to 1..SIZE.
    for col in 0..SIZE {
        clauses.push(vec![pos(var_index(0, col, col, SIZE))]);
    }

    let mut solver = Solver::new(SIZE * SIZE * SIZE, clauses);
    let sat = solver.solve();

    println!("Latin Square (N = {}) SAT = {}", SIZE, sat);

    if sat {
        for row in 0..SIZE {
            let mut line = String::with_capacity(SIZE * 2);
            for col in 0..SIZE {
                let mut value = 0;
                for symbol in 0..SIZE {
                    let var = var_index(row, col, symbol, SIZE);
                    if solver.value_of(var) == Some(true) {
                        value = symbol + 1;
                        break;
                    }
                }
                line.push(char::from_digit(value as u32, 10).unwrap());
                if col + 1 != SIZE {
                    line.push(' ');
                }
            }
            println!("{}", line);
        }
    }
}
