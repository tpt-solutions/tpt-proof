# Spike: Z3 Proof Reconstruction

Status: **spike complete, findings recorded.** This is the research item in TODO.md ("Research spike: Z3 proof-reconstruction strategy"). It answers whether Z3's `unsat` answers can be turned into kernel-checkable proofs, which spec.txt §3 and Principle 5 require before a result can be called `Verified`.

## Experiment

Z3 5.3.3, with proof production enabled, on a small valid VC:

```
(set-option :produce-proofs true)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= x 10))
(assert (not (<= (+ x y) (+ 10 y))))
(check-sat)
(get-proof)
```

Output: `unsat`, followed by a proof of 10 lines and 336 bytes. The proof is built from:

- `asserted`, which introduces each hypothesis;
- `rewrite`, which rewrites `(<= (+ x y) (+ 10 y))` to `(<= x 10)`. This is an arithmetic normalization, so it is a theory step, not a propositional one;
- `monotonicity`, which lifts that rewrite under `not`;
- `mp` (modus ponens) and `unit-resolution`, which combine the facts into `false`.

## What this shows

1. Z3 can produce a proof object for an `unsat` VC, so the reconstruction route exists in principle.
2. The propositional steps (`asserted`, `mp`, `unit-resolution`, `monotonicity`) are standard and map directly onto the kernel's implication and equality rules.
3. The arithmetic step (`rewrite`) is the hard part. The kernel has no arithmetic theory, so a rewrite like `x + y <= 10 + y  ↔  x <= 10` would have to be justified separately.

## Strategy this points to

- **Kernel-checked fragment first.** Accept a proof only when every step is one the kernel can check: propositional steps, and equalities over uninterpreted terms, which the kernel already has. Arithmetic rewrites are not accepted yet.
- **Arithmetic steps by certificate.** For linear integer arithmetic, a Farkas-style certificate (nonnegative coefficients that combine the facts into `0 < 0`) can be checked by a short kernel rule. That is the next spike.
- **Anything else is `Failed`, not `Verified`.** A VC whose proof uses an unchecked step keeps the current `SolverUnsat` outcome, which is explicit that no certificate has been checked.

## Limits and open questions

- Only one small VC was tested. Proofs for loop VCs, which use quantifier-free arithmetic with fresh constants, are likely larger and may use more theory steps. That needs measurement before committing to a checker design.
- The proof format is Z3's own term language. A parser for it is needed, and it is a trusted-base question whether that parser is part of the kernel. spec.txt says it is not: parsing is untrusted, because the kernel checks what the parser produces.
- Proof size and checking time are unmeasured on realistic VCs.

## Recommendation

Do not wire proof reconstruction into the driver yet. The next step is a measured spike on the existing loop and call VCs: record how many steps they produce and which rules appear. If the propositional and equality fragment covers them, implement a checker for that fragment. If arithmetic dominates, start with the Farkas certificate rule.

## Measured spike: the loop and call VCs

This section answers the measurement the recommendation above asked for. It is a spike result, not a checker.

### Method

- The VCs are the 49 distinct encoded scripts that the `tpt-proof-mir` test suite produces. That suite covers straight-line code, branches, loops with invariants, calls with contracts, and signed and unsigned division.
- The scripts were captured with a temporary local hook in `smt::check` that wrote each encoded script to a directory. The hook was reverted before anything was committed.
- Each script was run with `(set-option :produce-proofs true)` and `(get-proof)` in place of `(get-model)`, under Z3 5.3.3.

### Results

- 32 of 49 VCs are `unsat`. The other 17 are counterexamples, which have no proof to check.
- The 32 proofs total about 53 KB. The largest is about 6 KB and 104 lines. These are small.
- 22 of the 32 proofs contain at least one arithmetic `rewrite` step.
- Rule counts across all 32 proofs: `rewrite` 282, `monotonicity` 231, `mp` 158, `trans` 137, `asserted` 78, `and-elim` 32, `unit-resolution` 40, `hypothesis` 1, `commutativity` 1, `symm` 1, `lemma` 1.
- The proofs contain no `th-lemma`, no Farkas-style step, and no nonlinear step. Z3 settled the arithmetic by simplification, not by a certificate.

### What the arithmetic `rewrite` steps are

They are ground normalizations and comparison rewrites, for example:

- `(* (- 1) 2)` rewrites to `(- 2)`, and `(+ 0 (- 2))` rewrites to `(- 2)`.
- `(= (= _2 0) false)` after `(= (- 2) 0)` is simplified to `false`.
- `(< 4294967295 (+ 1 __h2))` rewrites to `(not (<= (+ 1 __h2) 4294967295))`.

Many other `rewrite` steps are propositional, such as `(not (not p))` to `p`, `(= p p)`, and `(= x $x)` abbreviations.

### Revised recommendation

This replaces the earlier recommendation to start with a Farkas checker. Farkas certificates do not appear in the measured proofs, so a Farkas checker would not accept any of them.

1. **Build the propositional and equality checker first.** It covers `asserted`, `mp`, `unit-resolution`, `and-elim`, `monotonicity`, `trans`, `symm`, `commutativity`, and the `let`-bound term language. It needs a parser for Z3's proof s-expressions, which is untrusted, and the kernel checks what it produces.
2. **Add ground arithmetic evaluation** as the next rule. Numeral arithmetic over `+`, `-` and `*`, and the comparisons of two numerals, can be decided by evaluation and recorded as one checked step. This covers the normalizations in the first group above.
3. **Add linear normalization** for the remaining `rewrite` steps: equalities between linear integer terms with the same meaning. This is the largest trusted addition, because each normalization rule needs a justification. Scope it to the rules that appear in these 32 proofs, and record each one.
4. **Leave `lemma` and any `th-lemma` as `Failed`** until a sample shows they are needed. The measured set has one `lemma`.

Before step 3, check how many distinct `rewrite` shapes the 32 proofs use. That count sets the size of the normalization trust, and it can be measured with the same dump.

### Limits of this measurement

- Only the MIR fixture VCs were measured. Real filesystem contracts may use more theory.
- Checking time was not measured. The proofs are small, so the cost is probably low, but that is not yet shown.
- The capture hook is not in the repository. Reproducing the measurement needs the hook, which takes a few lines in `smt::check`.

## First slice: reconstruction in the kernel

This section records what was built after the measured spike. It is not a complete checker.

### Decision: propositional steps are a trusted tautology rule

The spike recommended a derivational checker for the propositional fragment. This slice instead adds one trusted primitive, `ProofTerm::Taut`. It accepts a formula when a truth table over its letters shows it true, with ground arithmetic atoms evaluated by the kernel. The reasons:

- Z3's propositional steps are many small rewrites (`(not (not p))`, `(or false p)`, `(= p p)`, and similar). Deriving each one from primitive rules needs a rule per shape. A truth table covers them all with one rule.
- The rule makes the kernel classical. The proofs need excluded middle for the final step (refuting `not goal` gives `goal`), so the spike's intuitionistic-style checker would need an extra axiom anyway.
- The trust is small and stated: the truth-table check, the encodings of `not`, `and`, `or`, `iff` in `formula.rs`, and the integer evaluation in `arith.rs`. `kernel/AUDIT.md` lists them.

This is a trust expansion beyond the spike's plan. If the project wants a derivational propositional checker instead, `Taut` can be replaced by derivations one shape at a time, without changing the translator's structure.

### What is implemented

- Kernel: `Formula` and its encodings, `ProofTerm::Taut`, the built-in `Int` sort and operations, and `axioms::declare_standard` with eight integer axioms.
- Contract crate, `reflect.rs` (untrusted): reads Z3's proof, translates each step, and hands the term to `Kernel::check_proof`. Propositional steps become a tautology lemma applied to their premises. Rewrites are tautologies, or instances of a standard axiom. Equalities use `trans`, `symm`, `refl`, `cong` and `Leibniz`.
- `smt::verify` asks Z3 for a proof. It returns `Outcome::Verified` only when the kernel accepts the translated proof. A solver `unsat` that the kernel does not confirm returns `Outcome::Unchecked` with the reason.

### What was measured

- The 32-proof MIR corpus from the spike was not re-run. The capture hook is not in the repository, so the figures above are not re-measured.
- Fixtures and probe VCs, through the solver: a conjunction, modus ponens, a negated comparison, congruence of `+`, and the spike's bounded-sum example are `Verified` (a ground fact, `2 + 3 = 5`, was also `Verified` in a probe that is not in the tests). An invalid VC returns `Failed` with a counterexample. A VC that needs a Farkas certificate (`x < y` implies `x + 1 <= y`) returns `Unchecked`.
- The probe also showed the next gap. Z3's arithmetic normalization (`x - y` to `x + (-1) * y`, and `a <= b` to `a + (-1) * b <= 0`) needs one more axiom per normal form. The spike asked for the distinct shapes to be counted first. That count has not been done, so no normalization axioms were added.

### Not covered, and reported as `Unchecked`

- `th-lemma`, including Farkas certificates. This is the step that makes `x < y` imply `x + 1 <= y`.
- Arithmetic normalization beyond the equations listed above.
- `ite`, `div`, `mod`, and non-linear arithmetic beyond uninterpreted `*`.
- `lemma`, `quant-inst`, and the other rules not in `reflect.rs`'s dispatch.

### Next steps

1. Count the distinct rewrite shapes in the 32-proof corpus, as the spike asked, and decide which normal forms to axiomatize.
2. Reconstruct `th-lemma` with Farkas certificates. Each certificate is a linear combination, which the kernel can check by Taut and the cancellation axioms.
3. Re-run the MIR corpus through `smt::verify` and record the reconstructed fraction.

### Corpus measurement with the MIR fixtures

The 30 MIR fixtures in `crates/tpt-proof-mir/tests/fixtures` were run through the driver twice, once as before and once with `TPT_PROOF_VERIFY=1`, which calls `smt::verify`.

- Default mode: 38 VCs proved (solver `unsat`, not kernel-checked), 19 counterexamples, and the rest unsupported.
- Proof mode: 11 of the 38 proofs are accepted by the kernel. The other 27 are reported as unchecked, with these causes:
  - 11 use Z3's indexed `th-lemma` rules, which are not reconstructed (Farkas certificates);
  - 6 are `rewrite` steps that need arithmetic normalization;
  - 5 are `monotonicity` steps over normalized forms;
  - 2 were a translation bug, now fixed: Z3 gives one premise per changed argument, and the translator matched premises by position. They now stop at arithmetic normalization, like the rest of that group;
  - 3 contain `div` or `mod` terms, which are not translated.
- The first run accepted 6. The gap to 11 was a translation bug: a conjunction of one formula, which the translator builds and Z3 prints as the formula itself, did not match. It is fixed and has a regression test.
- Timing: the 30 fixtures take about the same time in both modes on this machine (7 s each run), so proof mode adds little cost at this size. This is the whole corpus of fixtures, not a benchmark.

## Second slice: linear arithmetic in the kernel

This slice follows the revised recommendation above. It adds two primitive rules for linear integer arithmetic, each checked by a small module of the kernel (`linear.rs`, `farkas.rs`) and recorded in `kernel/AUDIT.md`. Neither is an axiom.

- `ProofTerm::Linear(a, b)` proves `a -> b` for two constraints `t <= s` whose differences `t - s` have the same linear form. Over the integers that makes them equivalent. This covers Z3's normalizations such as `x <= -1 + y` to `x + (-1) * y <= -1`.
- `ProofTerm::Farkas(premises, coefficients)` proves `P_1 -> ... -> P_k -> false`, where each premise is `t <= s` or `t <= s -> false` (`not (t <= s)`, which is `s + 1 <= t`). Non-negative coefficients must combine the premises into a variable-free positive constant. This is the certificate of a `th-lemma` clause: the negated literals are the premises, and a tautology turns the refutation into the clause.

The reflection side reads `(_ th-lemma arith farkas c1 ... cn)` with its clause, and it proves the rewrites of an integer comparison by `Linear`, or a comparison that is valid over the integers (`x <= 1 + x` to `true`) by a Farkas refutation of its negation.

### Measurement after the second slice

The same 30 MIR fixtures, run with the pinned nightly through `tpt-proof verify` with `TPT_PROOF_VERIFY=1`. The solver answers `unsat` on 38 assertions in both modes, and 19 counterexamples are reported in both modes.

| | Before | After |
|---|---|---|
| Kernel-checked proofs | 11 | 26 |
| Unchecked | 27 | 12 |

The 12 that remain:

- 4 `monotonicity` steps over integer equations whose sides differ by normalization (`0 + (-1) * 2` against `0 + neg 2`). The linear rule covers only `<=`; extending it to `=` needs the same form check up to sign.
- 2 indexed rules other than the Farkas shape. They were not inspected.
- 1 `rewrite` that scales a comparison (`2 * x <= 255` against `x <= 127`). This is integer rounding, not a linear equivalence, so it needs a rule of its own.
- 1 `rewrite` and 1 `monotonicity` over an equation with a non-linear or unnormalized side.
- 3 terms with `div` or `mod`, which are not translated.

The corpus counts are reproducible on this machine with the pinned nightly. They are a measurement of the fixtures, not a benchmark.

### Third slice: equations and identities

The linear rule now covers equations as well as `<=`, matched with either sign. A new primitive, `ProofTerm::Identity(t, s)`, proves `t = s` when the two terms have the same linear form. `monotonicity` over an equation accepts a premise only for each changed argument, as Z3 gives it, and proves the unchanged ones by reflexivity.

On the same 30 fixtures, the kernel now accepts 31 of 38 solver proofs (26 before this slice). The 7 that remain:

- 3 terms with `div` or `mod`, which are not translated.
- 2 `th-lemma` steps of kind `assign-bounds`, a bound-propagation lemma whose coefficients are signed. The Farkas rule takes non-negative coefficients, and the sign convention of Z3's `assign-bounds` has not been decoded.
- 1 `rewrite` that scales a comparison (`2 * x <= 255` to `x <= 127`), which needs integer rounding.
- 1 `rewrite` of an equation to a conjunction of two comparisons (`x = 0` to `x <= 0 and 0 <= x`). It needs a derived rule from the equation to each conjunct.

### Fourth slice: array laws and division

The kernel now declares the array theory (`select`, `store`, `const_array` and three laws) and integer division (`div`, `mod` and three Euclidean laws for a positive divisor). Both are trusted axioms, listed in `kernel/AUDIT.md`, and both are used only when a checked proof needs them. The reflection translates `div`, `mod`, `select` and `store`, and it reads Z3's `true-axiom` and the symmetry of an equation. The linear rules now treat a non-linear term as an opaque integer, so an identity between two opaque terms can be checked.

On the 30 original fixtures the kernel result is the same as before: 31 of 38 solver proofs. The five array and division fixtures add the rest. Across all 35 fixtures, 38 of 53 solver proofs are kernel-checked, and 15 are not. The remaining 15 are:

- 8 `th-lemma` steps. The ones inspected are the `assign-bounds` kind described above. The others were not inspected, and may be array-theory lemmas.
- 2 Farkas lemmas whose argument list includes premise proofs.
- 2 translator terms that use `ite` (the signed division and remainder), which the kernel's terms do not have.
- 1 `rewrite` that scales a comparison.
- 1 `rewrite` that needs `mod` bounds as a fact about a comparison, for example `4 <= x mod 4` is false. The axioms state the bounds, but the reflection does not yet derive the comparison from them.
- 1 normalization of an equation between linear terms, which is not yet reconstructed.

The last item is why `0 <= x mod 4 < 4` is proved by the solver but not by the kernel. The test in `tests/arrays.rs` pins that state.

### Fifth slice: remainder bounds

Z3 proves `0 <= x mod 4 < 4` by rewriting each comparison to `true`, or `4 <= x mod 4` to `false`. The reflection now refutes such a comparison, or its negation, from the division laws. For each `t mod k` with a positive numeral `k`, it applies `mod_nonneg` and `mod_lt_divisor` to `t` and `k`, with the ground proof of `0 < k`. These facts are added as premises of a Farkas certificate, whose coefficients are 0 or 1. The search tries each choice and the kernel checks the one that works. The Farkas rule now also accepts strict comparisons, since over the integers `t < s` is `t + 1 <= s`.

Across the 35 fixtures, 39 of 53 solver proofs are kernel-checked, and 14 are not. The remaining 14 are the same kinds as before, less the two remainder rewrites: 8 `th-lemma` steps, 2 Farkas lemmas with premise proofs in their arguments, 2 `ite` terms from signed division, one comparison that scales by a constant, and one equation normalization.

### Sixth slice: bound-propagation lemmas

Z3's `assign-bounds` lemma is a clause over bounds on integers. Its printed coefficients (`1 -1`) do not match the literals and do not follow the Farkas convention, so they are not used. The reflection negates the clause, and searches for a certificate whose coefficients are 0 or 1. The kernel checks each attempt, and the first that refutes the negated clause is used. The loop fixture's bound assertions are now kernel-checked.

Across the 35 fixtures, 41 of 53 solver proofs are kernel-checked, and 12 are not. The remaining 12 are 3 `triangle-eq` lemmas (equalities, not yet a Farkas clause), 3 indexed rules with a short head that the reflection does not recognize, 2 theory lemmas with premise proofs in their arguments, 2 `ite` terms, one comparison that scales by a constant, and one equation normalization.

### Seventh slice: bare Euclidean lemmas, and the `triangle-eq` investigation

A bare `(_ th-lemma arith)` clause that states the Euclidean identity `t = k * (t div k) + (t mod k)` among `false` literals is now reconstructed as an instance of the `div_mod_euclid` axiom, with `0 < k` by evaluation. No new axiom is needed. The count of solver proofs is unchanged at 41 of 53: the lemma is accepted where it occurs, but the fixtures' other obstacles are still there.

The `triangle-eq` lemmas were investigated and not reconstructed. The simple form, `a = b`, or `not (a <= b)`, or `not (b <= a)`, needs the antisymmetry of the integers, which is not a consequence of the existing axioms. A version of that axiom was tried and then removed: it did not change any fixture's result, and it would add a trusted axiom without a review. The other form, with a `not (a = b)` literal, has not been decoded.

### Eighth slice: integer rounding by Farkas certificates

An equivalence of two comparisons that differ in scale, such as `2 * x <= 255` and `x <= 127`, is now proved in each direction by linear arithmetic. The implication `A -> B` assumes `A` and refutes `not B` with a certificate whose coefficients are 0, 1 or 2, then applies double negation. The search tries up to three coefficient choices per premise when there are at most four premises. The kernel checks each attempt, so the search cannot make a false equivalence accepted. No new axiom.

Across the 35 fixtures, 42 of 53 solver proofs are kernel-checked, and 11 are not. The remaining 11 are 3 indexed rules with a short head the reflection does not recognize, 5 theory lemmas with premise proofs in their arguments, 2 `ite` terms from signed division, and 1 equation rewritten to a conjunction. The last one needs equality reasoning that is not yet in the kernel without an axiom.

### Ninth slice: Farkas steps with premise proofs

Z3 also writes a Farkas step as `((_ th-lemma arith farkas c1 ... cn) p1 ... pn false)`, where each `pi` proves a comparison (or its negation) and the step concludes `false`. The reflection proves each premise, builds the Farkas certificate from the premise formulas, and applies it to the premise proofs. Z3's coefficients are used when the kernel accepts them; otherwise they are searched, as for the other lemma kinds. No new axiom.

Across the 35 fixtures, 44 of 53 solver proofs are kernel-checked, and 9 are not. The remaining 9 are 4 indexed rules with a head the reflection does not recognize (the `triangle-eq` forms, which need the antisymmetry axiom that was left out), 2 theory lemmas of another shape, 2 `ite` terms from signed division, and 1 equation rewritten to a conjunction.
