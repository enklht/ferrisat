# Ferrisat

An experimental Boolean satisfiability (SAT) solver in Rust.

## Examples

```sh
cargo run --example n_queens
cargo run --example pigeonhole
cargo run --example latin_square
cargo run --example sudoku
```

## Usage

The binary takes the filename of a `.cnf` file in DIMACS format as its argument.

```sh
cargo run -- formula.cnf
```

The final line is `true` if a solution exists, or `false` otherwise.

## Tests

```sh
cargo test --lib --test solver
```

The tests in `tests/cnf_data.rs` use datasets from [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).
Place them under `data/` using the paths in `tests/cnf_data.rs`.
