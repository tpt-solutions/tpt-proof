# Changelog

All notable changes to `tpt-proof-mir` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- The MIR translator (`translate`): optimized MIR of integer and boolean functions
  becomes verification conditions, with straight-line code, `if`, `return`, and
  overflow checks on `+`, `-` and `*`.
- Division and remainder, signed and unsigned, with Rust's truncation rules and
  checks for a zero divisor and for `MIN / -1`.
- Loops with `#[invariant(line, cond)]`, checked by the entry, havoc and
  preservation rule. A loop without an invariant is reported with its line.
- `#[requires]` and `#[ensures]` contracts, read from the function's doc markers,
  and direct calls that use the callee's contract as a summary.
- Shared references to scalars, modelled by their pointee.
- The `tpt-proof-mir` driver, which prints one verdict per assertion, reports
  unsupported constructs by name, and exits 0 only if everything is proved.
- `TPT_PROOF_FORMAT=json` for one JSON object per line.
- `TPT_PROOF_VERIFY=1` for kernel-checked results, and `TPT_PROOF_CACHE` for the VC
  cache directory.
- Fixtures in `tests/fixtures/` and a driver test suite that checks each one.
