# Changelog

All notable changes to `tpt-proof-macros` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- `#[requires(cond)]`, which checks `cond` on entry with `debug_assert!`, and
  records a doc marker for the MIR translator. Repeat it for several conditions.
- `#[ensures(|result| cond)]`, which checks the return value. The body runs in a
  closure, so `return` and `?` work.
- `#[runtime_check(cond)]`, an alias of `requires` that matches spec.txt §3.
- `#[invariant(line, cond)]`, a loop invariant for the verifier, with no runtime
  check.
- `#[refined(value < bound)]` on a struct, which adds a checked `new` and a getter.
- `#[state_machine(A, B, ...)]` on a struct, which adds sealed state markers and a
  `PhantomData` state field.
- The `==>` operator in contract conditions, rewritten to `!(a) || (b)`.
- A `cfg(tpt_proof_verify)` split: the runtime checks are switched off when the
  verifier runs, so the translator sees only the function's own code.
