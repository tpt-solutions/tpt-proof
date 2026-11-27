# Design note: conditional terms, and division by a variable

Status: proposal. No code. The two questions need a decision before any change to the kernel.

Background: after the fifteenth reflection slice, the kernel checks 49 of 53 solver proofs across the 35 fixtures. The four that remain are two `ite` terms from signed division and remainder, one equation rewritten to a conjunction, and one ensures that divides by a variable (`div_guarded`).

## 1. Conditional terms (`ite`)

Z3 writes the signed `/` and `%` of Rust with `ite` terms over unsigned `div` and `mod`. The VC language has `Expr::Ite`, so the solver handles it. The kernel's terms (`Term`) have no conditional, so a proof that mentions one cannot be stated.

Options:

- **A. Add `Term::Ite(Prop, Term, Term)` to the kernel.** This is the direct form. It changes the checker (sort checking of the condition and branches), the built-in arithmetic (evaluate `ite` on ground conditions), the library format, and the Lean export. It is a change to the trusted base, so it needs the review that `kernel/AUDIT.md` requires. Cost: moderate; the design is clear.
- **B. Fresh constants with defining axioms.** Replace each `ite(c, a, b)` by a fresh constant `t` and add `c -> t = a` and `not c -> t = b`. This is conservative, because `t` is defined only by these two laws. Each law is a new axiom, so it needs the same review, once per term shape rather than once per proof. Nothing in the checker changes.
- **C. Case split in the reflection.** A goal mentioning `ite(c, a, b)` is proved in each case of `c`, by the tautology rule on `c`. This needs the rule that rewrites under a case split, which the kernel does not have. Not recommended.

Recommendation: **B**. It keeps the checker unchanged, the trusted addition is two laws per `ite` shape, and each law is a closed integer fact that a reviewer can check by reading. If the number of shapes grows, move to **A**.

Decision needed: approve B (new axioms, reviewed as in the `le_antisymm` change), or A (checker change, reviewed as a kernel change).

## 2. Division by a variable

The VC `div_guarded` needs `y * (x div y) + (x mod y) = x` for a variable `y` with `0 < y`. The Euclidean identity is a non-linear fact: the product `y * q` has two variables. Farkas certificates are linear, so the search cannot refute the goal, however many coefficients it tries. Division by a numeral is linear and is already handled.

Options:

- **A. Leave it unsupported.** The solver proves the ensures, and proof mode reports it as unchecked. This is honest and costs nothing. Recommended for now.
- **B. A product rule.** A certificate may multiply two linear constraints (for example `0 < y` and `q <= bound`) and add the products, then use the same linear check. The kernel would check the product by polynomial arithmetic over the integers. This is a new trusted rule of moderate size, similar to the Farkas rule, and it would also cover other non-linear VCs.
- **C. A new axiom for each division shape.** Rejected: the identity is a general law, and per-shape axioms are not a proof of it.

Recommendation: **A now, B later**, only if a fixture or a user needs non-linear division. The remaining proof obligation is genuinely non-linear, and option B is a real kernel addition that should be justified by a need.

Decision needed: confirm A for now, or ask for B to be scoped in detail.
