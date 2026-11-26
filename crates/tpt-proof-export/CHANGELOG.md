# Changelog

All notable changes to `tpt-proof-export` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- `export(&kernel, &[Lemma])`, which writes the kernel's sorts, symbols and axioms
  as Lean declarations, with each axiom's justification as a comment, and each
  lemma as a Lean `theorem`.
- `Lemma`, the name, claim and proof term of a theorem to export.
- `ExportError`, with `BadName`, `UnknownTheorem`, `UnknownAxiom` and
  `UnsupportedRule`, so an unsupported rule is an error, not a silent omission.
- A test that runs the output through `lean`, skipped when `lean` is missing.

### Fixed

- A free propositional variable in an axiom or lemma was written unbound, and Lean
  rejected the file. Each one is now declared once as a global `Prop` constant, which
  is how the kernel reads it: a name means one fixed proposition.
