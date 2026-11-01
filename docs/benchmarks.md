# Benchmarks

Status: **kernel benchmark recorded; Z3 and end-to-end timings pending.**

## Kernel checking time

Measured with `cargo bench -p tpt-proof-kernel` (release build, Windows, Rust stable).
Source: `crates/tpt-proof-kernel/benches/check.rs`.

| Workload | Size | Time |
|---|---|---|
| Modus ponens chain | 10 | 35.6 µs |
| Modus ponens chain | 50 | 49.5 µs |
| Modus ponens chain | 100 | 75.5 µs |
| Nested identity | 10 | 6.1 µs |
| Nested identity | 50 | 15.6 µs |
| Nested identity | 100 | 42.3 µs |

Checking time grows roughly linearly with proof size in this range.

## Stack depth (a limit found by the benchmark)

The checker recurses once per level of proof nesting. A chain of 1,000 modus ponens steps, and a nested identity of depth 1,000, both overflow the default main-thread stack on Windows (`STATUS_STACK_OVERFLOW`). The benchmark caps sizes at 100 for this reason.

This is a real limit of the trusted kernel. Options:

1. Run `check_proof` on a thread with a larger stack. This is a small change, and it moves the limit without changing the checker.
2. Rewrite the checker with an explicit stack. This removes the limit, but it changes the trusted code, so it needs the second-reviewer step in `kernel/AUDIT.md`.

Recommendation: option 1 now, option 2 when a real proof needs more depth than the larger stack allows.

## Pending

- Z3 check time per VC, for the translator's fixtures (`tpt-proof-mir`).
- End-to-end time for `tpt-proof verify` on the fixtures.
