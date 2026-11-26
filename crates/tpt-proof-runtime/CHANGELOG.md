# Changelog

All notable changes to `tpt-proof-runtime` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- `runtime_check!(cond)`, a `debug_assert!` that names the condition in its
  message. It compiles to nothing in release builds.
- `replay::run`, which calls a function under chosen inputs and reports `Passed`,
  `Confirmed` (a contract failed) or `Panicked` (a panic for another reason). Panics
  are caught, so many replays can run in one test.
- `property::check`, which runs a property over a `proptest` strategy with
  shrinking, behind the optional `proptest` feature. The feature is off by default,
  so the crate has no dependencies unless it is enabled.
