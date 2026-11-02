# Benchmarks

Status: **kernel and contract-level Z3 timings recorded; translator-fixture and end-to-end timings pending.**

## Kernel checking time

Measured with `cargo bench -p tpt-proof-kernel` (release build, Windows). Source: `crates/tpt-proof-kernel/benches/check.rs`. The work runs on a thread with a 256 MB stack (see "Stack depth").

| Workload | Size | Time |
|---|---|---|
| Modus ponens chain | 10 | 27.8 µs |
| Modus ponens chain | 100 | 107.9 µs |
| Modus ponens chain | 1,000 | 1.05 ms |
| Nested identity | 10 | 4.3 µs |
| Nested identity | 100 | 33.7 µs |
| Nested identity | 1,000 | 368.6 µs |

Checking time grows roughly linearly with proof size over this range.

## Stack depth

The checker recurses once per level of proof nesting. On the default main-thread stack (about 1 MB on Windows), a proof 1,000 steps deep overflowed with `STATUS_STACK_OVERFLOW`.

The benchmark now checks on a thread with a 256 MB stack, which runs the depth-1,000 proofs. The kernel itself is unchanged.

Callers that check deep proofs should do the same: run `check_proof` on a thread with a large enough stack. An iterative checker would remove the need, but it changes the trusted code, so it needs the second-reviewer step in `kernel/AUDIT.md`. That is the next step if proofs need more depth than a large stack allows.

## Z3 check time

Measured with `cargo run -p tpt-proof-contract --release --example z3_timing` (Z3 5.3.3, Windows). Each VC is checked five times through `smt::check`, which encodes the script, starts `z3`, and parses its answer. The table gives the median wall-clock time of one check.

| VC | Median | Outcome |
|---|---|---|
| Loop: `count_to_n` (invariant preserved and exit) | 49.9 ms | `SolverUnsat` |
| Branch: `abs` | 49.8 ms | `SolverUnsat` |
| Straight-line chain, 10 steps | 48.4 ms | `SolverUnsat` |
| Straight-line chain, 100 steps | 47.7 ms | `SolverUnsat` |
| Straight-line chain, 1,000 steps | 49.1 ms | `SolverUnsat` |

These times are almost entirely process start-up for `z3` (about 50 ms). None of the workloads reaches the point where solving dominates, and the chain times do not grow with length in this range. The fixtures are contract-level VCs built in `examples/z3_timing.rs`, not the MIR translator's output, so they do not yet measure the translator's real VCs.

## Pending

- Z3 check time per VC for the translator's fixtures (`tpt-proof-mir`). The workloads above come from `wp::generate`, not from MIR.
- End-to-end time for `tpt-proof verify` on the fixtures. This needs the pinned nightly driver environment.
