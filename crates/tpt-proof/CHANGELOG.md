# Changelog

All notable changes to `tpt-proof` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- `prelude`, which re-exports the Layer 1 types, `Kernel`, `ProofTerm`, `Prop`,
  `Theorem`, the tactic types, `library`, `tactics`, and the attribute macros
  `requires`, `ensures`, `invariant`, `refined`, `runtime_check` and `state_machine`.
- Interactive proofs (`tactics::Proof`): `intro`, `intro_forall`,
  `intro_individual`, `assumption`, `apply_hyp`, `apply_axiom`, `apply_theorem`,
  `exact`, `case_split`, `induct`, `rewrite_hyp`, `rewrite_axiom`,
  `rewrite_theorem`, `tauto`, `auto`, and `qed`, which has the kernel check the
  whole term.
- `Proof::suggestions`, which lists the tactics that apply to the focused goal.
- `tauto`, which closes a propositional goal from its hypotheses with the
  tautology rule, and `auto`, which tries `assumption` and then `tauto`.
- The lemma library (`library`): `save`, `load` and `load_with_lemmas`. Loading
  replays every declaration through the kernel and checks every lemma.
- Dependency reports (`report::dependency_report`): each theorem, its axioms and
  their justifications.
- `examples/first_proof.rs`: a theorem by tactics, an axiom, the dependency report
  and the Lean export.
- `examples/induction.rs`: addition defined by recursion, and a proof of
  `add(n, zero) = n` by induction.
- Tests for the derive attributes, the contract macros, the tactics, the library,
  and a `trybuild` suite for misuse of the attributes.

### Documentation

- A README with an overview of the layers, a tactic reference and examples.
