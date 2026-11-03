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
