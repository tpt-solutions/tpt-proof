# Spike: Z3 Proof Reconstruction

Status: **spike complete, findings recorded.** This is the research item in TODO.md ("Research spike: Z3 proof-reconstruction strategy"). It answers whether Z3's `unsat` answers can be turned into kernel-checkable proofs, which SPEC.md §3 and Principle 5 require before a result can be called `Verified`.

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
- The proof format is Z3's own term language. A parser for it is needed, and it is a trusted-base question whether that parser is part of the kernel. SPEC.md says it is not: parsing is untrusted, because the kernel checks what the parser produces.
- Proof size and checking time are unmeasured on realistic VCs.

## Recommendation

Do not wire proof reconstruction into the driver yet. The next step is a measured spike on the existing loop and call VCs: record how many steps they produce and which rules appear. If the propositional and equality fragment covers them, implement a checker for that fragment. If arithmetic dominates, start with the Farkas certificate rule.
