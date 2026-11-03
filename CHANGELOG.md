# Changelog

All notable changes to this project are recorded here. The project is pre-alpha,
and nothing is published yet.

## Unreleased

### Fixed

- **Kernel soundness.** The tautology rule reads the atom `false` as the constant
  false, but generalization could bind that name, so a proof of an arbitrary
  proposition was accepted. Reserved names (`false`, `#r`, numerals, and the other
  built-in names) are now rejected as binders in proofs and declared propositions,
  as atoms in `Taut`, as function and predicate names, and as inductive
  constructors.
- **Solver hangs.** The Z3 driver kills a solver that runs past its timeout plus
  five seconds, and reports `Timeout`, instead of waiting forever.
- **Lean export.** A free propositional variable in an axiom or a lemma was written
  unbound, and Lean rejected the file. It is now declared once as a global `Prop`
  constant, which is how the kernel reads it: `A` names one fixed proposition.

### Added

- `tpt-proof verify` options: `--timeout`, `--z3-path`, `--json`, `--help`.
  The driver reads `TPT_PROOF_TIMEOUT_MS`, `TPT_PROOF_Z3` and `TPT_PROOF_FORMAT=json`.
- `tpt-proof report <library>`, `tpt-proof export <library> [--out <file>]` and
  `tpt-proof doctor`, which checks rustup, the pinned toolchain, z3, the driver and
  lean, and says how to fix what is missing.
- The `tauto` tactic, which closes a propositional goal from its hypotheses with the
  tautology rule.
- `examples/induction.rs`: addition defined by recursion, and a proof of
  `add(n, zero) = n` by induction.
- Tests that need z3 or lean skip with a message when the tool is missing, instead
  of being marked `#[ignore]`. The helper is `tests-support/tools.rs`.
- A quickstart in the README.
- `examples/first_proof.rs`: a theorem by tactics, an axiom, the dependency report,
  and the Lean export, which `lean` checks.
- The facade prelude re-exports the tactics, the `library` module and `invariant`.

### Documentation

- `docs/kernel-logic.md` describes the tautology rule, Leibniz, case analysis,
  induction and the scope limit of `Taut`.
- `kernel/AUDIT.md` records the soundness fix.
