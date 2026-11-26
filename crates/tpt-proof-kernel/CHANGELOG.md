# Changelog

All notable changes to `tpt-proof-kernel` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The crate is pre-alpha
and not published, so the entries under Unreleased describe its current state.

## Unreleased

### Added

- Propositions with implication, propositional and individual quantification,
  equality, and predicate symbols (`terms::Prop`).
- Sorted individuals, with the built-in sort `Int` and its operations and
  numerals (`arith`).
- The proof checker (`checker`): `Var`, `Lam`, `App`, `Axiom`, `Const`, `TyLam`,
  `TyApp`, `IndLam`, `IndApp`, `Refl`, `Sym`, `Trans`, `Cong`, `Leibniz`, `Cases`,
  `Induct` and `Taut`.
- The opaque `Theorem` type, which only `Kernel::check_proof` can construct, and
  the axiom dependencies it records.
- Trusted axioms with a written justification, declared by `Kernel::declare_axiom`
  and listed in `kernel/AUDIT.md`. `axioms::declare_standard` declares the integer
  laws.
- The tautology rule (`taut`), a truth table over at most 16 letters, which makes
  the kernel classical.
- Boolean formulas encoded into propositions (`formula`): `not`, `and`, `or`,
  `iff`, `true` and `false`.
- Inductive sorts (`Kernel::declare_inductive`) with generated induction axioms,
  constructors, and the case and induction premises they need.
- Definitions: `define_function` (non-recursive, conservative) and structural
  recursion by `define_by_recursion` and `define_by_recursion_with_params`.
- Unit, negative, property and reserved-name tests, and a benchmark in
  `benches/check.rs`.

### Fixed

- Reserved names (`false`, `#r`, numerals, and the other built-in names) are
  rejected as binders in proofs and declared propositions, as atoms in `Taut`, as
  function and predicate names, and as inductive constructors. Before this, the
  tautology rule could be used to prove an arbitrary proposition, because
  generalization over the name `false` changed what the atom meant.
- A constructor named `"0"` is rejected by `declare_inductive`, since the numeral
  path would otherwise shadow it.

### Documentation

- `docs/kernel-logic.md` describes the tautology rule, Leibniz substitution, case
  analysis, induction, and the scope limit of `Taut`.
- `kernel/AUDIT.md` records the scope of the kernel and the soundness fix. The
  hand audit has not been done.
