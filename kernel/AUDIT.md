# Kernel Audit

Status: **not yet audited.** The kernel is in early Phase 1 (SPEC.md §12).

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
| Inductive types and induction | Not implemented (see design doc: sort question open) |
| Inductive types, `Constr`, `Match` | Not implemented |
| `define_function` with termination checking | Not implemented |
| Equality over ground terms: refl, symm, trans, congruence, with declared function arities | Implemented |
| Leibniz substitution | Not implemented |
| Bounded arithmetic axioms | Not implemented |
| Rust-semantics axioms | Not implemented |

## Trusted axioms

None. The kernel ships with no built-in axioms. Implication introduction and elimination are primitive rules.

## Reviewers

| Role | Name | Date |
|---|---|---|
| Primary author | TPT Solutions | 2026 |
| Second reviewer (kernel and axiom changes) | **[TODO: name]** | |
| Independent audit | **[TODO: name]** | |

## Change log

- 2026: initial kernel with simply-typed implication logic, opaque theorems, and dependency tracking.
- 2026: added propositional quantification with capture-avoiding substitution, alpha-equivalence, and the generalization side condition. Added property-based tests (fixed-seed generator, no dependencies).
- 2026: added equality over ground terms of uninterpreted function symbols (refl, symm, trans, congruence). Function symbols are declared with an arity, and every term is arity-checked.
- 2026: added individual variables, predicate symbols, and quantification over individuals with the same generalization side condition as propositional quantification. Axioms, theorems, and assumptions must be closed.

## Rules for changes

- Zero dependencies (enforced in CI).
- Under 5,000 lines of source (enforced in CI).
- `#![forbid(unsafe_code)]`.
- Any new axiom needs a justification in its doc comment, a dedicated PR, a second reviewer, and an entry here.
