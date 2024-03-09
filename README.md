# CDCL SAT Solver

This is a CDCL SAT Solver purely as a learning exercise for myself.

The solver itself is in `solver.rs` with helper data structures in `slot_map.rs` and `fixed_size_stack.rs`.
The solver is used to solve the following problems:

- sudoku (`sudoku.rs`)
- master key (`master_key.rs`)
- master key using minisat (`master_key_ms.rs`)
- festival event scheduling (`festival_scheduler.rs`)

To test solving example sudoku and master key problems:

```bash
cargo run --release
```

There are only tests for `solver.rs` and `sudoku.rs`

## References

https://codingnest.com/modern-sat-solvers-fast-neat-underused-part-1-of-n/ \
https://codingnest.com/modern-sat-solvers-fast-neat-and-underused-part-2-of-n/ \
https://codingnest.com/modern-sat-solvers-fast-neat-and-underused-part-3-of-n/ \
https://users.aalto.fi/%7Etjunttil/2020-DP-AUT/notes-sat/overview.html \
https://www.princeton.edu/~chaff/publication/DAC2001v56.pdf \
http://minisat.se/downloads/MiniSat_v1.13_short.pdf \
