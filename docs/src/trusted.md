# What is trusted

A verification result is only as good as the parts it relies on. This page lists those parts, the status of each, and what you must believe to accept a result. The authoritative review record is `kernel/AUDIT.md`. The kernel has **not yet been independently audited**.

## The trusted computing base

**The proof kernel** (`crates/tpt-proof-kernel`) is the trusted core. It has no dependencies, and CI keeps it under 5,000 lines. It contains:

- the proof checker, which decides whether a proof term proves a proposition;
- the opaque `Theorem` type, which only the kernel can construct;
- the primitive rules: implication, quantifiers over propositions and individuals, equality (reflexivity, symmetry, transitivity, congruence, and Leibniz substitution), case analysis and induction on inductive sorts;
- the tautology rule `Taut`, which decides a propositional formula by a truth table;
- the linear arithmetic rules `Linear`, `Identity` and `Farkas`, which check that two comparisons or terms have the same linear form, and that a set of constraints combines into a contradiction (`linear.rs`, `farkas.rs`);
- the encodings in `formula.rs` (`not`, `and`, `or`, `iff`) and the integer evaluation in `arith.rs`. Both must match the usual semantics, and both are trusted.

If the kernel accepts a theorem, the theorem follows from the axioms in its dependency report and nothing else. That is the guarantee; the rest of this page is about what the axioms are and what sits outside the kernel.

## Axioms

An axiom is a proposition the kernel accepts without proof. Each one is recorded with a justification, and `tpt-proof report <library>` lists the axioms each theorem depends on.

- **The integer axioms** are added only when a caller asks for them (`axioms::declare_standard`). There are eight, each over `Int`, each true over the integers. They are listed in `kernel/AUDIT.md`.
- **Generated axioms.** Declaring an inductive sort generates its induction axiom, and each definition by recursion or `define_function` generates a defining equation. These are conservative over fresh symbols, so they add no contradiction, but they are still axioms and must be reviewed by name.
- **Rust-semantics axioms** (what the verifier may assume about Rust values and memory) are not built. This is deliberate: each one needs its own review, and none is in the trusted base today.

## Outside the kernel: checked, not trusted

These components produce proofs or propositions, and the kernel checks what they produce. A bug in them can cause a failed proof, never an accepted false theorem.

- **The tactics** (`tpt-proof::tactics`) build proof terms. A wrong tactic produces a term the kernel rejects at `qed`. Note that `tauto` and `auto` apply the tautology rule without deciding it first, so an unprovable goal fails at `qed`, not when the tactic is called.
- **The proposition parser** (`tpt-proof::prop`) only builds a `Prop`. A parser bug can give the wrong proposition, which is then the statement that is proved, so read what `prop!` produces for anything that matters.
- **The library loader** (`tpt-proof::library::load`) replays every declaration through the kernel and checks every lemma again.
- **The Lean export** is checked by `lean`, which is a separate implementation, when you run it. Without `lean`, the export is unchecked.

## Outside the kernel: trusted by default

The verifier for Rust code uses an external solver, and some of its steps are trusted unless you opt in.

- **Z3** is run as a subprocess (`z3` on the PATH, or `--z3-path`). By default its `unsat` verdict is trusted. Set `TPT_PROOF_VERIFY=1` and the driver asks Z3 for a proof and has the kernel check it. A result the kernel does not accept is reported as `Unchecked`, not verified. Not every Z3 step can be reconstructed yet: integer equations under normalization, scaling by a constant, `ite`, `div` and `mod` are reported as `Unchecked`. Linear arithmetic is checked by two kernel rules, `Linear` (equivalent normalized comparisons) and `Farkas` (contradictions, the certificates of `th-lemma` clauses); their trust is in `kernel/AUDIT.md`.
- **The MIR translator** (`tpt-proof-mir`) turns Rust into verification conditions. A mistake there, such as a missed overflow check or a wrong model of an operator, can produce conditions that are easier than the real program. The supported subset is listed in the crate, and any construct outside it is reported by name rather than assumed.
- **The VC cache** stores `unsat` and counterexample results on disk, keyed by the encoded script and the timeout. Anyone who can write to the cache directory can plant a result, so do not share a cache directory between machines you do not trust. The cache never stores `Verified` results, because a cached proof would be forgeable in the same way.
- **Contracts used as summaries.** When one function calls another, the callee's contract is assumed while verifying the caller. The callee is verified separately; if its contract is not verified, the caller's result depends on an assumption that nothing has checked.

## Status

| Component | Status |
|---|---|
| Kernel checker and primitive rules | Implemented, not audited |
| Tautology rule and formula encodings | Implemented, trusted, not audited |
| Integer axioms | Implemented, listed in `kernel/AUDIT.md` |
| Rust-semantics axioms | Not built |
| Z3 proof reconstruction | Partial; see the list of unchecked steps above |
| Lean export check | Requires `lean` on the PATH |
| Independent audit | Not started |

When you report a result, state which of these you relied on, and run with `TPT_PROOF_VERIFY=1` for anything that must not depend on the solver's verdict.

## Arrays

The MIR translator models an array of integers as an SMT array, with `select` for a read and `store` for a write. A read's bounds check is the assertion that rustc's MIR contains, so it is verified like any other assertion. In default mode the solver's theory of arrays is trusted, like the rest of the solver's answers. In proof mode the kernel checks array terms with three trusted axioms, `select_store_same`, `select_store_other` and `select_const`, which are the standard laws of the array theory. A VC that uses an array shape the reflection does not yet translate is reported as unchecked, never as verified. The integer `div` and `mod` have three trusted Euclidean axioms for a positive divisor (see `kernel/AUDIT.md`).
