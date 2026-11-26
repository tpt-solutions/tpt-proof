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

- Kernel: integer division and remainder (`div`, `mod`, with Euclidean axioms for a positive divisor) and integer arrays (`select`, `store`, `const_array`, with the array laws). Trusted axioms, recorded in `kernel/AUDIT.md`. Proof mode now checks array terms and the division laws: 38 of 53 solver proofs across the 35 fixtures are kernel-checked.
- Verification of arrays of integers. The MIR translator reads `[T; N]` values, element reads and writes, `[v; N]` and literal arrays, and rustc's bounds checks become assertions. The solver's array theory decides them. Proof mode does not yet check array terms; they are reported as unchecked.
- The `auto` tactic: closes a goal by `assumption`, or else by `tauto`.
- Kernel: two linear integer arithmetic rules, `ProofTerm::Linear` (equivalent normalized comparisons) and `ProofTerm::Farkas` (linear contradictions, the certificates of Z3's `th-lemma` clauses). Neither is an axiom; both are in `kernel/AUDIT.md`.
- Proof reconstruction reads Z3's `th-lemma` (Farkas) steps and the comparison normalizations. On the 30 MIR fixtures, the kernel now accepts 31 of 38 solver proofs, up from 11.
- The `simplify` tactic: rewrites the goal with a list of equations (`Rule::Hyp`,
  `Rule::Axiom`, `Rule::Theorem`) until none applies, at most 64 times. Names are
  checked before any rewriting.
- `tpt_proof::prop::parse` and the `prop!("...")` macro, which read propositions
  from text: atoms, `->`, `forall p.` and `false`. Parsing is untrusted; the kernel
  checks the proofs of whatever proposition is read.
- The mdBook gained a tutorial, a cookbook and a "what is trusted" page. The
  cookbook recipes are tests, so the documented code is compiled and run.
- CI: a Windows build-and-test job and a book build job. Neither has run on GitHub yet.
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

- `docs/src/gallery.md` and `examples/gallery/`: five verified-Rust examples with the CLI output recorded from the pinned driver, including counterexamples and the two open reflection gaps.

- `docs/kernel-logic.md` describes the tautology rule, Leibniz, case analysis,
  induction and the scope limit of `Taut`.
- `kernel/AUDIT.md` records the soundness fix.
