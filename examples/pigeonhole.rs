use cdcl_rs::*;

fn var_index(num_holes: usize, pigeon: usize, hole: usize) -> usize {
    pigeon * num_holes + hole
}

fn main() {
    const NUM_PIGEONS: usize = 3;
    const NUM_HOLES: usize = 2;
    let pos = Lit::pos;
    let neg = Lit::neg;

    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    // Each pigeon is in at least one hole.
    for pigeon in 0..NUM_PIGEONS {
        let mut clause = Vec::with_capacity(NUM_HOLES);
        for hole in 0..NUM_HOLES {
            clause.push(pos(var_index(NUM_HOLES, pigeon, hole)));
        }
        clauses.push(clause);
    }

    // Each pigeon is in at most one hole.
    for pigeon in 0..NUM_PIGEONS {
        for hole1 in 0..NUM_HOLES {
            for hole2 in (hole1 + 1)..NUM_HOLES {
                clauses.push(vec![
                    neg(var_index(NUM_HOLES, pigeon, hole1)),
                    neg(var_index(NUM_HOLES, pigeon, hole2)),
                ]);
            }
        }
    }

    // Each hole contains at most one pigeon.
    for hole in 0..NUM_HOLES {
        for pigeon1 in 0..NUM_PIGEONS {
            for pigeon2 in (pigeon1 + 1)..NUM_PIGEONS {
                clauses.push(vec![
                    neg(var_index(NUM_HOLES, pigeon1, hole)),
                    neg(var_index(NUM_HOLES, pigeon2, hole)),
                ]);
            }
        }
    }

    let mut solver = Solver::new(NUM_PIGEONS * NUM_HOLES, clauses);
    let sat = solver.solve();

    println!(
        "Pigeonhole (pigeons = {}, holes = {}) SAT = {}",
        NUM_PIGEONS, NUM_HOLES, sat
    );
}
