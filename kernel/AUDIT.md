# Kernel Audit

Status: **not yet audited.** The kernel is in early Phase 1 (spec.txt §12).

The kernel source lives in [crates/tpt-proof-kernel](../crates/tpt-proof-kernel). This file tracks what has been reviewed and by whom.

## Scope

| Item | Status |
|---|---|
| Propositions (atoms, implication) | Implemented |
| Proof terms: `Var`, `Const`, `Axiom`, `Lam`, `App` | Implemented |
| Proof checker (`checker.rs`) | Implemented |
| Opaque `Theorem` (private fields, crate-private constructor) | Implemented |
| Axiom declaration with justification; dependency tracking | Implemented |
| Assumptions (`assume`) | Implemented |
| Propositional quantification (`forall p. A`; `TyLam`, `TyApp`) with the generalization side condition | Implemented |
| Quantification over individuals (`forall x. A`; `IndLam`, `IndApp`) with the generalization side condition and capture-avoiding instantiation | Implemented |
| Predicate symbols applied to terms | Implemented |
| Multiple sorts; inductive declarations (constructors, positivity trivially satisfied by first-order arguments); kernel-generated induction axioms | Implemented (trusted: the sort must be generated freely by its constructors) |
| Induction on inductive types (`Induct`): one premise per constructor, with a hypothesis for each recursive argument. Sound under the free-generation assumption of the induction axiom | Implemented (primitive rule, not an axiom) |
| Case analysis on inductive types (`Cases`): one premise per constructor, no hypotheses for recursive arguments | Implemented (trusted: the sort must be generated freely by its constructors, as for induction axioms) |
| Non-recursive definitions (`define_function`): one conservative equation over a fresh symbol | Implemented (the equation is recorded as an axiom named `symbol_def`) |
| Structural recursion (`define_by_recursion`): one defining equation per constructor, recursive calls on recursive arguments only | Implemented (conservative; termination by structure) |
| Recursion with extra parameters (first argument structural; `define_by_recursion_with_params`) | Implemented |
| General termination checking beyond structural recursion | Not implemented |
| Equality over ground terms: refl, symm, trans, congruence, with declared function arities | Implemented |
| Leibniz substitution (`Leibniz`): from `t = s` and `P[x := t]`, derive `P[x := s]` | Implemented |
| Boolean formulas (`formula.rs`): `not`, `and`, `or`, `iff`, `true`, `false`, encoded into propositions | Implemented (the encodings are trusted; see below) |
| Tautology rule (`ProofTerm::Taut`, `taut.rs`): a formula true under every valuation of its letters, with ground arithmetic atoms evaluated; at most 16 letters | Implemented (primitive trusted rule; it makes the kernel classical) |
| Built-in integers (`arith.rs`): sort `Int`, numerals, `+`, `-`, `*`, `neg`, `<=`, `<`, and ground evaluation in `i128` | Implemented (trusted meaning of numerals and operators) |
| Integer axioms (`axioms::declare_standard`): eight laws over `Int` | Implemented (trusted axioms, listed below) |
| Bounded (modular) arithmetic axioms | Not implemented. The VC language uses unbounded `Int`, so the standard axioms are over `Int` |
| Rust-semantics axioms | Not implemented |

## Trusted axioms

Built-in: none. `Kernel::new` declares the sort `Int` and the operations `+`, `-`, `*`, `neg` and the predicates `<=`, `<` with their usual meaning, but it declares no axioms. Implication, quantifiers, and equality are primitive rules. `axioms::declare_standard` adds the eight integer axioms below; a caller opts in.

Trusted primitive: the tautology rule (`ProofTerm::Taut`). It accepts a formula when a truth table over its letters shows it true, and it evaluates ground atoms with the built-in arithmetic. It makes the kernel classical: `not not p -> p` is accepted with no excluded-middle axiom. Its soundness depends on two things, which are also trusted: the encodings in `formula.rs` must be classically equivalent to the connectives they stand for (`not p` as `p -> false`, `and` and `or` as second-order encodings, `iff` as two implications), and the built-in evaluation in `arith.rs` must match the usual integer semantics. Numerals must be canonical (no leading zeros), and an overflow in `i128` makes an atom a letter, which can only make the rule reject more.

The integer axioms, each a closed proposition over `Int`, each true over the integers:

- `le_cancel_right_fwd`: `x + z <= y + z -> x <= y`.
- `le_cancel_right_bwd`: `x <= y -> x + z <= y + z`.
- `lt_def_fwd`: `x < y -> (y <= x -> false)`.
- `lt_def_bwd`: `(y <= x -> false) -> x < y`.
- `add_cancel_left_fwd`: `z + x = z + y -> x = y`.
- `add_cancel_left_bwd`: `x = y -> z + x = z + y`.
- `add_comm`: `x + y = y + x`.
- `add_zero`: `x + 0 = x`.

These were chosen for the proofs that Z3 produces for the VCs in the reconstruction tests. They do not cover Z3's arithmetic normalization (for example `x - y` as `x + (-1) * y`) or its Farkas certificates (`th-lemma`), which are not reconstructed.

Generated by the kernel: one induction axiom per `declare_induction` call. It is trusted only as far as the sort is generated freely by its constructors. Each such axiom must be listed in the review of this file.

Generated by the kernel: one `symbol_def` axiom per `define_function` call, and one defining equation per constructor for each `define_by_recursion` call. Both are conservative definitions over fresh symbols, so they add no contradiction, but each is still an axiom in the environment and is listed here by name when reviewed.

Primitive rules added since the initial review: `Leibniz` (equality substitution), `Cases` (case analysis on an inductive sort), and `Induct` (structural induction on an inductive sort). They are part of the checker, not axioms. `Cases` and `Induct` are sound given the same assumption as the induction axiom, that the constructors generate the sort freely. `Leibniz` uses only the equality rules already in the checker. All three are part of the review scope.

## Reviewers

| Role | Name | Date |
|---|---|---|
| Primary author | TPT Solutions | 2026 |
| Independent audit | **[TODO: name]** | |

## Change log

- 2026: initial kernel with simply-typed implication logic, opaque theorems, and dependency tracking.
- 2026: added propositional quantification with capture-avoiding substitution, alpha-equivalence, and the generalization side condition. Added property-based tests (fixed-seed generator, no dependencies).
- 2026: added equality over ground terms of uninterpreted function symbols (refl, symm, trans, congruence). Function symbols are declared with an arity, and every term is arity-checked.
- 2026: added individual variables, predicate symbols, and quantification over individuals with the same generalization side condition as propositional quantification. Axioms, theorems, and assumptions must be closed.
- 2026: added multiple sorts, inductive declarations, and kernel-generated induction axioms. Constructor arguments are first-order, so positivity holds by construction. Sort-checked terms, predicates, and quantifiers.
- 2026: added structural recursion (`define_by_recursion`) with kernel-generated defining equations, checked for case coverage, sorts, and structural calls. Rejected definitions are rolled back.
- 2026: added extra parameters to structural recursion (`define_by_recursion_with_params`). Only the first argument must be structural.
- 2026: added read-only accessors for exporters and reports: `axioms`, `theorems`, `sorts`, `function_signature`, `functions`, `predicates`. They return existing data and change no checking logic.
- 2026: added Leibniz substitution (`ProofTerm::Leibniz`), checked for matching sorts and an exact instance of the motive. Exported to Lean as `Eq.subst`.
- 2026: added case analysis on inductive sorts (`ProofTerm::Cases`), with one premise per constructor built by `case_premise`. Same generalization side condition as `IndLam`. Not exported to Lean.
- 2026: made `Prop::subst_individual` public for the untrusted tactic layer, which uses it to rebuild goals for `rewrite`. The method is unchanged and no checking logic depends on the change.
- 2026: added structural induction on inductive sorts (`ProofTerm::Induct`), with `Kernel::induction_premise`. Each premise has a hypothesis for every recursive argument. The case-analysis and induction premises now share one construction (`constructor_premise`), and the side condition is checked by one function (`check_split`). Not exported to Lean.
- 2026: added non-recursive definitions (`define_function`). The body is checked before the symbol is declared, so it cannot be recursive, and the defining equation is recorded as the axiom `symbol_def`.
- 2026: added Boolean formulas (`formula.rs`) and the tautology rule (`ProofTerm::Taut`, `taut.rs`). This is a new trusted primitive: the kernel now accepts any formula that a truth table shows true, so it is classical. Reviewed scope: the encodings of the connectives and the truth-table check.
- 2026: added the built-in integers (`arith.rs`): sort `Int`, numerals (canonical decimal names, reserved), operations `+`, `-`, `*`, `neg`, predicates `<=` and `<`, and ground evaluation. The built-in names cannot be declared again (`KernelError::ReservedSymbol`). Reviewed scope: the evaluation.
- 2026: added `axioms::declare_standard` with the eight integer axioms listed under Trusted axioms. Each is justified in its doc comment.
- 2026: checks for the tautology rule. `tests/taut_property.rs` compares the kernel with an independent evaluator on 2,000 generated formulas. `tests/taut_lean.rs` (ignored; needs `lean`) compares the kernel with Lean 4 on 150 generated formulas, where Lean must prove what the kernel accepts and reject what it refuses. Neither check covers the encodings in `formula.rs`, which remain a review item.

## Rules for changes

- Zero dependencies (enforced in CI).
- Under 5,000 lines of source (enforced in CI).
- `#![forbid(unsafe_code)]`.
- Any new axiom needs a justification in its doc comment, a dedicated PR and an entry here.
