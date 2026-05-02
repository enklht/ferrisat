use ferrisat::*;

fn var_index(n: usize, row: usize, col: usize) -> usize {
    row * n + col
}

fn main() {
    const N: usize = 8;
    let pos = Lit::pos;
    let neg = Lit::neg;

    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    // Each row has at least one queen.
    for row in 0..N {
        let mut clause = Vec::with_capacity(N);
        for col in 0..N {
            clause.push(pos(var_index(N, row, col)));
        }
        clauses.push(clause);
    }

    // Each row has at most one queen.
    for row in 0..N {
        for col1 in 0..N {
            for col2 in (col1 + 1)..N {
                clauses.push(vec![
                    neg(var_index(N, row, col1)),
                    neg(var_index(N, row, col2)),
                ]);
            }
        }
    }

    // Each column has at least one queen.
    for col in 0..N {
        let mut clause = Vec::with_capacity(N);
        for row in 0..N {
            clause.push(pos(var_index(N, row, col)));
        }
        clauses.push(clause);
    }

    // Each column has at most one queen.
    for col in 0..N {
        for row1 in 0..N {
            for row2 in (row1 + 1)..N {
                clauses.push(vec![
                    neg(var_index(N, row1, col)),
                    neg(var_index(N, row2, col)),
                ]);
            }
        }
    }

    // Main diagonals (row - col constant): at most one queen.
    for diag in -(N as isize - 1)..=(N as isize - 1) {
        let mut cells = Vec::new();
        for row in 0..N {
            let col = row as isize - diag;
            if (0..N as isize).contains(&col) {
                cells.push((row, col as usize));
            }
        }
        for i in 0..cells.len() {
            for j in (i + 1)..cells.len() {
                let (row1, col1) = cells[i];
                let (row2, col2) = cells[j];
                clauses.push(vec![
                    neg(var_index(N, row1, col1)),
                    neg(var_index(N, row2, col2)),
                ]);
            }
        }
    }

    // Anti-diagonals (row + col constant): at most one queen.
    for diag in 0..=(2 * (N - 1)) {
        let mut cells = Vec::new();
        for row in 0..N {
            let col = diag as isize - row as isize;
            if (0..N as isize).contains(&col) {
                cells.push((row, col as usize));
            }
        }
        for i in 0..cells.len() {
            for j in (i + 1)..cells.len() {
                let (row1, col1) = cells[i];
                let (row2, col2) = cells[j];
                clauses.push(vec![
                    neg(var_index(N, row1, col1)),
                    neg(var_index(N, row2, col2)),
                ]);
            }
        }
    }

    let mut solver = Solver::new(N * N, clauses);
    let sat = solver.solve();

    println!("N-Queens (N = {}) SAT = {}", N, sat);

    if sat {
        for row in 0..N {
            let mut line = String::with_capacity(N);
            for col in 0..N {
                let var = var_index(N, row, col);
                let is_queen = solver.value_of(var).unwrap_or(false);
                line.push(if is_queen { 'Q' } else { '.' });
            }
            println!("{}", line);
        }
    }
}
