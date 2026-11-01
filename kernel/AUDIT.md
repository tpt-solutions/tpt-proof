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
| Universal quantification (`Forall`) | Not implemented |
| Inductive types, `Constr`, `Match` | Not implemented |
| `define_function` with termination checking | Not implemented |
| Equality (refl, symm, trans, congruence) | Not implemented |
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

## Rules for changes

- Zero dependencies (enforced in CI).
- Under 5,000 lines of source (enforced in CI).
- `#![forbid(unsafe_code)]`.
- Any new axiom needs a justification in its doc comment, a dedicated PR, a second reviewer, and an entry here.
