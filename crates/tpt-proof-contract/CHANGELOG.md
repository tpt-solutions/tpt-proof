# Changelog

All notable changes to `tpt-proof-contract` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- Verification conditions (`vc`): `Vc`, `Expr` and `Sort` (`Int` and `Bool`), with
  integer arithmetic, comparisons, `Ite`, and boolean connectives.
- SMT-LIB encoding of a VC (`smt::encode`, and `encode_with_proof` for proof mode).
- The Z3 driver (`smt`): `check` reports `SolverUnsat` for an `unsat` answer, and
  `verify` asks for a proof and reports `Verified` only when the kernel accepts it.
  Both report `Failed` with the counterexample, and `Timeout` or `Unknown`.
- `SolverConfig`, read from `TPT_PROOF_Z3` and `TPT_PROOF_TIMEOUT_MS`.
- Counterexample parsing (`smt::counterexample_values`).
- Proof reconstruction (`reflect::reconstruct`): Z3's proof objects are turned into
  kernel proof terms for asserted hypotheses, propositional steps, rewrites,
  `symm`, `trans`, `refl`, monotonicity, congruence and commutativity. Steps that are
  not translated make the result `Unchecked`.
- A VC result cache (`cache::VcCache`), keyed by the encoded script and the
  timeout with FNV-1a, on disk or in memory. Only `unsat` and counterexample results
  are stored.
- Weakest-precondition generation (`wp`): a small imperative `Function` with
  `Assign`, `Assert`, `Assume`, `If` and `While` statements, and integer ranges that
  model fixed-width overflow.
- A restricted contract expression language (`spec::parse`) for `requires` and
  `ensures` text.
- `examples/z3_timing.rs`, which times Z3 on contract-level VCs.
- Tests that need `z3` skip with a message when it is missing, instead of being
  marked `#[ignore]`.

### Fixed

- The solver is polled and killed after its timeout plus five seconds, and reported
  as `Timeout`. Before this, a hung `z3` could block verification forever.
- Congruence premises are matched to the arguments they justify during proof
  reconstruction.
