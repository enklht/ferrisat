use cdcl_rs::*;

const SIZE: usize = 9;
const BOX: usize = 3;

fn var_index(row: usize, col: usize, digit: usize) -> usize {
    (row * SIZE + col) * SIZE + digit
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

fn main() {
    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    // Each cell has exactly one digit.
    for row in 0..SIZE {
        for col in 0..SIZE {
            let mut vars = Vec::with_capacity(SIZE);
            for digit in 0..SIZE {
                vars.push(var_index(row, col, digit));
            }
            add_exactly_one(&mut clauses, &vars);
        }
    }

    // Each row has each digit exactly once.
    for row in 0..SIZE {
        for digit in 0..SIZE {
            let mut vars = Vec::with_capacity(SIZE);
            for col in 0..SIZE {
                vars.push(var_index(row, col, digit));
            }
            add_exactly_one(&mut clauses, &vars);
        }
    }

    // Each column has each digit exactly once.
    for col in 0..SIZE {
        for digit in 0..SIZE {
            let mut vars = Vec::with_capacity(SIZE);
            for row in 0..SIZE {
                vars.push(var_index(row, col, digit));
            }
            add_exactly_one(&mut clauses, &vars);
        }
    }

    // Each 3x3 box has each digit exactly once.
    for box_row in 0..BOX {
        for box_col in 0..BOX {
            for digit in 0..SIZE {
                let mut vars = Vec::with_capacity(SIZE);
                for row in 0..BOX {
                    for col in 0..BOX {
                        let r = box_row * BOX + row;
                        let c = box_col * BOX + col;
                        vars.push(var_index(r, c, digit));
                    }
                }
                add_exactly_one(&mut clauses, &vars);
            }
        }
    }

    let puzzle: [[usize; SIZE]; SIZE] = [
        [1, 0, 0, 0, 0, 7, 0, 9, 0],
        [0, 3, 0, 0, 2, 0, 0, 0, 8],
        [0, 0, 9, 6, 0, 0, 5, 0, 0],
        [0, 0, 5, 3, 0, 0, 9, 0, 0],
        [0, 1, 0, 0, 8, 0, 0, 0, 2],
        [6, 0, 0, 0, 0, 4, 0, 0, 0],
        [3, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 4, 0, 0, 0, 0, 0, 0, 7],
        [0, 0, 7, 0, 0, 0, 3, 0, 0],
    ];

    #[allow(clippy::needless_range_loop)]
    for row in 0..SIZE {
        for col in 0..SIZE {
            let value = puzzle[row][col];
            if value != 0 {
                let digit = value - 1;
                clauses.push(vec![Lit::pos(var_index(row, col, digit))]);
            }
        }
    }

    let mut solver = Solver::new(SIZE * SIZE * SIZE, clauses);
    let sat = solver.solve();

    println!("Sudoku SAT = {}", sat);

    if sat {
        for row in 0..SIZE {
            let mut line = String::with_capacity(SIZE * 2);
            for col in 0..SIZE {
                let mut value = 0;
                for digit in 0..SIZE {
                    let var = var_index(row, col, digit);
                    if solver.value_of(var) == Some(true) {
                        value = digit + 1;
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
