# Design: the `induct` tactic and an induction rule

Status: **accepted and implemented.** The recommendations in this document were followed, and the decisions are recorded under "Decisions" below. The rule adds a primitive to the trusted checker, so it is listed in `kernel/AUDIT.md`.

Relates to: TODO.md, Phase 4 tactics ("`induct` is pending"); `kernel/AUDIT.md`; `docs/design-inductive-types.md`.

## Problem

The kernel can already prove a property of an inductive sort by case analysis (`ProofTerm::Cases`), but only when no case needs the property for a smaller value. A case for `succ(n)` cannot use the claim for `n`, so case analysis cannot prove anything that needs induction, such as `forall n. n + 0 = n` over a recursive `plus`.

The kernel does have induction, through `Kernel::declare_induction`. That function adds an axiom with a predicate symbol `P`:

```text
for each constructor C(a1..an):  forall a. (P(ai) for each recursive ai) -> P(C(a))
implies  forall x:T. P(x)
```

A predicate symbol cannot be instantiated with a goal. A goal such as `x + 0 = x` is a proposition, not a predicate symbol, so the existing axiom cannot be applied to it. The `induct` tactic therefore needs a rule that takes the motive as a proposition.

## Proposal: a primitive induction rule

Add one proof term:

```text
Induct(x, S, P, cases)      proves  forall x:S. P
```

`P` is a proposition that may mention the individual variable `x`. `cases` has one proof per constructor, in declaration order. The proof for constructor `C(a1..an)` must prove the premise given by a new kernel function, `Kernel::induction_premise`:

```text
forall a1:S1 .. an:Sn.  (P[x := aj] for each recursive argument aj) -> P[x := C(a1..an)]
```

The binders are chosen to avoid the free individuals of `P`, as in `case_premise`. The hypotheses come after the binders and in argument order, which is the same shape `declare_induction` already uses. That makes the two rules agree.

### Example

Claim: `forall n:Nat. n = n`. The motive is `P(x) = (x = x)`. The premises are:

- `zero`: `zero = zero`, proved by `Refl(zero)`.
- `succ`: `forall a0:Nat. (a0 = a0) -> succ(a0) = succ(a0)`, proved by `IndLam(a0, Nat, Lam(ih, a0 = a0, Refl(succ(a0))))`.

The `succ` case uses the hypothesis `ih`, which the `Cases` rule could not provide.

### Soundness

The rule is sound under the same assumption that the kernel already makes for induction axioms: the constructors generate the sort freely, so every value of the sort is built from constructors. Under that assumption, structural induction holds for every proposition. The rule is no more trusted than `declare_induction`, and the existing kernel code already depends on the assumption.

The checker applies the same generalization side condition as `IndLam` and `Cases`. A hypothesis or axiom in scope that mentions `x` is rejected, because the generalized proof would then depend on one value of `x`.

## Kernel changes

1. `Kernel::induction_premise(variable, sort, motive, constructor) -> Result<Prop>`. It extends `case_premise` with a hypothesis `P[x := aj]` for each argument of sort `sort`. Estimated at 30 lines.
2. `ProofTerm::Induct(String, Sort, Prop, Vec<ProofTerm>)`, with a doc comment that states the premise and the trust assumption.
3. A checker arm. It is the same as `Cases`, except that it uses `induction_premise`. Estimated at 60 lines, including the side-condition checks.
4. Tests in `tests/induction.rs`:
   - `n = n` by induction, with the `succ` case using its hypothesis.
   - Rejection when a case omits the hypothesis, with the premise mismatch reported.
   - Rejection when the variable is mentioned by a hypothesis in scope.
   - Rejection when the sort is not inductive, or the case count is wrong.
   - A check that `induction_premise` avoids capturing a free individual of `P`.
5. The Lean export refuses `Induct` with `ExportError::UnsupportedRule`, as it does for `Cases`. An inductive sort has no Lean `casesOn` or recursor in the export, so the rule cannot be translated.

Trusted-base size: roughly 100 new lines in the kernel, which is well inside the 5,000-line budget. The kernel is currently about 1,670 lines.

## Facade: the `induct` tactic

`Proof::induct()` applies to a goal `forall x:T. P` where `T` is inductive:

- It leaves one goal per constructor `C`. Its target is `induction_premise(x, T, P, C)`, the same statement the kernel will check.
- The hypotheses of the goal carry over unchanged. A goal hypothesis that mentions `x` is rejected with `VariableInHypothesis`, as `case_split` does.
- The subgoal's inductive hypotheses appear in its target, not in its hypothesis list, because the premise has them as implications. The user opens each argument with `intro_individual`, opens each hypothesis with `intro`, and then closes the case. `intro_forall` is for propositional quantifiers, so it does not apply here. `intro_individual` is added with this change, because the design needs a way to name the case binders.
- The tactic builds `ProofTerm::Induct` from the subgoal proofs. `qed` checks the result.

`Suggestion::Induct` is offered when the focused goal is `forall x:T. P` with `T` inductive. The suggestion list currently offers `case_split` for the same shape, so `induct` is suggested alongside it.

## What this does not cover

- **Generalizing hypotheses.** A goal that has a hypothesis mentioning `x` is rejected. The standard fix is to move the hypothesis into the goal before inducting. That is a separate tactic, `generalize`, and it is a follow-up, not part of this design.
- **Nested or mutual induction.** `declare_inductive` allows only first-order arguments and does not support nesting. The rule inherits that restriction.
- **Well-founded induction** on other orders. Not needed for the current sorts.

## Decisions

Each question below was answered with the recommendation given. The answers are part of the design.

1. **`declare_induction` is kept.** It stays in the trusted base as an axiom for now. It is no longer needed for the tactic, and it can be deprecated and removed in a later change, once nothing depends on it.
2. **Inductive hypotheses are in the subgoal target.** This matches the kernel premise exactly. Hypotheses are not introduced automatically.
3. **The audit records `Induct` as a primitive rule.** It has an entry in the scope table, a line in the primitive-rules paragraph, and a change-log line. The independent-audit reviewer is still unnamed.

The implementation also adds `intro_individual`, which the facade lacked. The design had assumed it existed.

## Questions for the reviewer (answered above)

1. **Replace or keep `declare_induction`.** `declare_induction` adds an axiom to the trusted base. Once `Induct` exists, the axiom is derivable from the rule, so it could be removed from the TCB. The proposal keeps it for now, to avoid breaking existing users, and recommends deprecating it once `Induct` is in place.
2. **Hypotheses in the target or in the hypothesis list.** The proposal puts the inductive hypotheses in the target, to match the kernel premise exactly. The alternative is to introduce them automatically. That changes the tactic's behaviour, so it should be decided before implementation.
3. **Scope of the new rule in the audit.** `Induct` is a primitive rule, not an axiom, so it does not need an entry in the axiom list. It is still a change to the checker, so it needs an entry in the audit scope and a change-log line. The audit has no named independent reviewer yet.

## Implementation order

The kernel rule and its tests came first, then the export refusal, then the facade tactic, each checked on its own. The kernel change is reviewable without the tactic.

Possible follow-ups, not part of this design: the `generalize` tactic for goals with hypotheses that mention the variable, and deprecating `declare_induction`.
