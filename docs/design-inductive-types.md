# Design Proposal: Inductive Types and Recursion in the Kernel

Status: **implemented, with one deliberate change.** Multiple sorts, inductive declarations, induction axioms, and structural recursion are in the kernel. Structural recursion uses defining equations, not a recursor term; see the sections below.

## Where the kernel is now

- Propositions: atoms, implication, quantification over propositional variables, and equality between ground terms.
- Terms: uninterpreted function symbols with declared arities. A constant is a symbol of arity zero.
- Missing: any way to state facts about an *unbounded family* of values, such as all naturals, all lists, or all B-Tree nodes. Without that, the proof targets in spec.txt §9 (B-Tree balance, CoW atomicity) cannot be stated.

## What has to be decided

### 1. Individuals: a sort or the existing terms?

- **Option A (recommended): a single inductive sort, `Ind`, built from declared constructors.** Constructors are function symbols with a result sort of `Ind`. Terms stay ground unless we add variables.
- **Option B: multi-sorted terms.** More expressive (e.g. separate `Nat` and `List`), but every rule must carry sorts. More code in the TCB.

Recommendation: A, with sorts added later if a real need appears.

### 2. Recursion: recursors or definitional equations?

- **Option A (recommended): structural recursors only.** Each inductive type comes with a recursor `rec_T`, and its reduction rules are checked. Every definable function is total by construction, so no termination checker is needed in the kernel.
- **Option B: general recursive definitions with a termination checker.** Much more expressive, but the termination checker is a large, subtle component to put in the TCB.

Recommendation: A. Termination checking can move outside the kernel later, as an untrusted tactic that produces a recursor-based term.

### 3. Positivity

Constructor argument types must be strictly positive in the type being defined. Without this, the kernel accepts Russell-style paradoxes. Recommendation: check it at `declare_inductive`, and add tests that known non-positive declarations are rejected.

### 4. Induction

Induction is the recursor's type, so `induct` in Phase 4 becomes a tactic that applies the recursor. Recommendation: no separate induction rule.

## Proposed rules (sketch, not final)

```
declare_inductive(T, [C_1 : A_1 -> .. -> T, ..., C_n : ...])   -- positivity checked
rec_T : (motive) -> (case_i for each C_i) -> T -> motive
rec_T (C_i a..)  ==>  case_i a.. (rec_T a..)                   -- reduction, by equality rule
```

Equality rules from the existing kernel already let us use the reduction equations as theorems.

## Estimated size

- Kernel additions: ~400–600 lines, which fits the <5,000 LOC budget.
- Tests: positivity rejections, recursor typing, reduction on concrete values, and property tests over generated constructor trees.
- Audit: the new code is inside the TCB, so it needs the second-reviewer step in `kernel/AUDIT.md`.

## Revision after approval: a missing dependency

Implementing this design exposed a dependency the proposal did not list. Induction is the statement "for every individual x, P(x)", where P is a predicate on individuals. The recursor's motive (section 4) has the same shape. The kernel currently has neither:

- quantification over individuals (`forall x:Ind. ...`), and
- predicate symbols applied to terms (`P(t)` as a proposition).

Without them, the recursor can only be stated non-dependently, which defines functions but cannot prove anything about all values. The B-Tree and CoW goals in spec.txt §9 need the dependent form.

Adding them means three things beyond the approved design:

1. `Prop::Pred(symbol, args)`, a predicate applied to terms.
2. `Prop::ForallInd(name, body)` with an individual-level binder, plus capture-avoiding substitution of terms for individual variables.
3. Individual variables in `Term`, with their binding rules in the checker.

Items 2 and 3 are the same kind of change as propositional quantification, which is already implemented and tested, so the risk is manageable. They still add to the TCB and need the same review.

## Status after approval

Done: individual quantification, individual variables, and predicate symbols (items 1–3 above). Tests are in `crates/tpt-proof-kernel/tests/individuals.rs`.

Not done, and a new problem found while planning induction: with a single sort, the induction principle "for all x, if every constructor preserves P then P(x)" is only sound if every individual is built from the constructors. An uninterpreted constant `a` of sort `Ind` is an individual that no constructor built, so the principle would be false for any P that fails at `a`. Stating induction needs either:

- **Multiple sorts**, one per inductive type, so that "all values of type T" is a real set. This reverses the approved single-sort choice.
- **A membership predicate** `is_T(x)` with axioms that say every `is_T` value is a constructor application. The axiom needs disjunction and existentials, which the kernel does not have yet.

Recommendation: multiple sorts. It keeps each inductive type a real set and is the usual design. It needs your approval because it reverses option A.

## Implemented: multiple sorts and induction

Decision recorded: **multiple sorts**. Each inductive type is its own sort. `declare_inductive` declares the sort and its constructors. `declare_induction` generates the induction axiom for a predicate over the sort. The induction axiom is the usual induction principle, and it is trusted only as far as the sort is generated freely by its constructors (see `docs/kernel-logic.md`).

Tests: `crates/tpt-proof-kernel/tests/sorts.rs`, including induction over naturals, induction over a tree with two recursive arguments, and rejection of a predicate over the wrong sort.

Recursion: implemented as structural definitions (`define_by_recursion`) that generate one defining equation per constructor, rather than as a recursor term. This is a conservative extension and is what the approval covered (structural only, no termination checker in the kernel). Recursion over several arguments remains open.

## Decisions needed

0. Include individual-level quantification and predicate symbols (items 1–3 above) in this design, or defer induction and implement only constructors and non-dependent recursion for now?

1. Approve Option A for individuals (single sort `Ind`).
2. Approve Option A for recursion (structural recursors, no kernel termination checker).
3. Approve positivity checking at declaration time.

Once these are approved, implementation can start.
