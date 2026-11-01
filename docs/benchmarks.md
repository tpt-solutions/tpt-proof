# Benchmarks

Status: **kernel benchmark recorded; Z3 and end-to-end timings pending.**

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

## Pending

- Z3 check time per VC, for the translator's fixtures (`tpt-proof-mir`).
- End-to-end time for `tpt-proof verify` on the fixtures.
