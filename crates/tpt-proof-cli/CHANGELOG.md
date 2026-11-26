# Changelog

All notable changes to `tpt-proof-cli` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- `tpt-proof verify <file.rs>`, which runs the MIR driver and prints one verdict per
  assertion, with `--timeout <ms>`, `--z3-path <path>` and `--json`. It sets
  `TPT_PROOF_TIMEOUT_MS`, `TPT_PROOF_Z3` and `TPT_PROOF_FORMAT` for the driver.
- `tpt-proof report <library>`, which prints the dependency report of a lemma
  library, loaded and checked through the kernel.
- `tpt-proof export <library> [--out <file>]`, which writes a library's lemmas as Lean.
- `tpt-proof doctor`, which checks rustup, the pinned toolchain, `z3`, the driver and
  `lean`, and prints the fix for each one that is missing.
- `--help` and `--version`.
- The `TPT_PROOF_MIR` and `TPT_PROOF_TOOLCHAIN` variables, which locate the driver and
  its toolchain.
