# tpt-proof TODO

Legend: `[ ]` todo · `[x]` done. Milestones are in **bold**. Source of truth for design: `spec.txt`.

## Decisions made

- [x] License: dual **MIT OR Apache-2.0**, copyright TPT Solutions (spec section 11 said MIT-only; update it)
- [x] Crate naming: `tpt-proof-*` (spec's `axiom-*` is renamed)
- [x] MIR access: pinned **nightly** (`rustc_private` / `stable_mir`)
- [x] Z3 integration: **shell out to the `z3` binary**, parse its proof output (no C++ linking, outside the TCB)

## Former open questions (resolved: recommendations adopted)

- [x] Kernel logic: **simply-typed lambda calculus with higher-order logic (HOL-style, LCF)**; no dependent types. Typed `Lam`/`Forall` in `ProofTerm` are consistent with this. Write up the rules in Phase 1 before coding.
- [x] Kernel has **zero external dependencies** (std only, even `dev-dependencies` kept out of the kernel crate; property tests live in a separate test crate). CI enforces it.
- [x] Z3 proof reconstruction: Z3 only *finds* certificates and its verdict is never trusted. Start with a narrow fragment (QF_LIA and QF_UF) and check certificates (e.g. Farkas coefficients) with kernel-checked rules. Anything not reconstructible is reported as `Failed`, never accepted. Research spike at the start of Phase 3 confirms feasibility.
- [x] Toolchain: pin one specific nightly date in `rust-toolchain.toml` at Phase 0 and bump deliberately. The kernel and non-MIR crates must also build on **stable** (MSRV = latest stable minus 2 releases; decide the exact number at Phase 0).
- [x] Integers: model `usize`/`u64` etc. as **bounded naturals with explicit modular ops**. Plain `+`/`-`/`*` generate overflow VCs (prove no overflow); `wrapping_*`/`checked_*` map to their own operations.
- [x] Rust-semantics axioms: **minimal, safe-subset only**. Each axiom lives in `axioms.rs` with a doc comment (statement, justification, reference to Rust reference/Miri/RustBelt). Adding one requires a dedicated PR plus a second reviewer, and is recorded in `AUDIT.md`.

## Still needs you (can't be decided by me)

- [ ] GitHub org/repo name (e.g. `TPT-Solutions/tpt-proof`?)
- [ ] Reserve crate names on crates.io (`tpt-proof`, `tpt-proof-kernel`, ...)
- [ ] `CODEOWNERS`; name at least one second reviewer for kernel and axiom changes
- [ ] Security contact email for `SECURITY.md`

## Phase 0: Repo foundation

- [x] `git init`, `.gitignore`, default branch
- [x] `LICENSE-MIT`, `LICENSE-APACHE` (Apache text verified against apache.org)
- [x] `README.md` with license and contribution blurb
- [x] Copy/rename `spec.txt` to `SPEC.md`; update section 10 (crate names) and section 11 (licensing)
- [x] Cargo workspace root `Cargo.toml` with `license = "MIT OR Apache-2.0"`, `authors`/`repository`
- [x] `rust-toolchain.toml` pinning nightly + components (`rustc-dev`, `llvm-tools`) (stable for now; the nightly pin lands with `tpt-proof-mir` in Phase 3)
- [x] `rustfmt.toml`, `clippy` config, `deny.toml` (cargo-deny: licenses must be MIT/Apache-2.0 compatible)
- [x] CI (GitHub Actions): build, test, fmt, clippy, cargo-deny, kernel line-count check (<5,000 LOC)
- [x] `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `SECURITY.md` (soundness bug reporting policy)
- [x] Per-crate `Cargo.toml` stubs for the crates listed below
- [x] `docs/` skeleton (mdBook or similar)

### Crate skeleton (`crates/`)

- [x] `tpt-proof-kernel` (the trusted kernel; also at `kernel/` with `AUDIT.md`)
- [x] `tpt-proof-core` (Layer 1: refined types, state machines, units)
- [x] `tpt-proof-contract` (Layer 2: contracts, VCs, SMT)
- [x] `tpt-proof` (Layer 3: proof DSL, tactics; the user-facing facade and prelude)
- [x] `tpt-proof-runtime` (Layer 4)
- [x] `tpt-proof-mir` (MIR analysis, translation)
- [x] `tpt-proof-cli`
- [ ] `stdlib/{collections,sync,io}`, `examples/filesystem`, `proofs/kernel_soundness`
- [ ] Proc-macro crate(s) for `#[refined]`, `#[requires]`, `#[theorem]`, etc. (proc macros must live in their own crate)

## Phase 1: Kernel foundation

- [x] Formal write-up of the logic (syntax, typing rules, inference rules) before coding
- [x] `Type`, `Proposition`, `ProofTerm` AST (`terms.rs`)
- [x] Opaque `Theorem` type, constructible only by the kernel
- [x] Contexts, variable binding, capture-avoiding substitution
- [ ] Proof checker (`checker.rs`): Var, Lam, App, Forall, Constr, Match, Axiom (partial: Var, Lam, App, Axiom, Const, TyLam, TyApp done; Constr, Match pending)
- [ ] Inductive type declarations + positivity check
- [ ] Recursive function definitions + termination checking
- [ ] Equality: refl, symm, trans, congruence
- [ ] Trusted axioms (`axioms.rs`): logical, equality, bounded arithmetic
- [ ] Rust-semantics axioms (safe subset only), each documented and justified
- [x] Axiom-dependency tracking per theorem
- [ ] Kernel API: `declare_axiom`, `declare_inductive`, `define_function`, `check_proof`, `assume` (partial: declare_axiom, declare_theorem, check_proof, assume done; declare_inductive and define_function pending)
- [x] Unit tests, property-based tests, and negative tests (bogus proofs must be rejected)
- [x] Enforce <5,000 LOC and zero deps in CI
- [x] `AUDIT.md` (scope, reviewers, status)
- [x] **Milestone: kernel checks simple proofs**
- [ ] Hand audit; publish the audit report

## Phase 2: Layer 1, type-level specs

- [ ] `#[refined(...)]` macro (e.g. `value < total_blocks`) (Index<N> done by hand; the derive needs a proc-macro crate)
- [ ] Compile-time checks via const eval plus simple bound queries (const-checked constructor done; bound queries pending)
- [ ] `#[state_machine(...)]` type-state macro (hand-written FileHandle done; the derive is pending)
- [x] Unit-correctness types (blocks / bytes / sectors)
- [x] Ghost state and phantom type helpers
- [x] `tpt_proof::prelude`
- [ ] trybuild compile-fail tests, docs, examples (compile_fail doctests done; trybuild and examples pending)
- [x] **Milestone: write and check type-level specs** (hand-written; derive macros pending)

## Phase 3: Layer 2, contracts

- [ ] Contract macros: `#[requires]`, `#[ensures]`, `#[invariant]`, `#[assert]`, `==>` operator
- [ ] Research spike: Z3 proof-reconstruction strategy
- [ ] MIR extraction (`tpt-proof-mir`): desugar, monomorphize, resolve ownership
- [ ] Verifiable subset enforcement with clear errors for unsupported features (Phase 1 subset: safe Rust, no closures, no `dyn`, no raw pointers, no FFI)
- [ ] Ownership/borrow model (linear resources, loans)
- [ ] VC generation (`vc.rs`): weakest precondition, loops via invariants, overflow/bounds checks (WP, loop havoc, and range (overflow) obligations done; array bounds pending; source language is a model, not MIR)
- [x] SMT-LIB encoding and `z3` subprocess driver (timeouts, resource limits) (not run against real z3 here: 2 ignored tests need z3 on PATH)
- [ ] Proof-producing reflection: convert Z3 output to kernel proof terms; fail if not checkable
- [ ] Counterexample extraction and reporting (raw solver model only; not parsed into values)
- [ ] Result states: Verified / Unverified / Failed / Timeout, never silent fallback (Outcome done; Verified is unreachable until proof reflection exists)
- [ ] Caching and incremental verification
- [ ] `tpt-proof-cli` (`cargo tpt-proof verify`), diagnostics UX
- [ ] **Milestone: verify simple function contracts**

## Phase 4: Layer 3, interactive proofs

- [ ] DSL macros: `#[theorem]`, `#[lemma]`, `arbitrary()`, `assume()`, `show()`, `by {}` (not started: needs the proc-macro crate; tactics are the Rust API for now)
- [ ] Tactic framework (untrusted): `case_split`, `apply`, `induct`, `simplify`, ... (intro, intro_forall, apply_*, assumption, exact done; case_split, induct, simplify pending)
- [x] Each tactic step emits a proof term that the kernel checks
- [ ] Interactive mode: goal display and suggested next steps (Goal Display done; suggested next steps pending)
- [ ] Lemma library and theorem dependency/axiom reports (declare_theorem done; a shared lemma library is pending)
- [x] **Milestone: write and check interactive proofs** (via the tactics API)

## Phase 5: Layer 4, runtime verification

- [ ] `#[runtime_check]` and spec-to-assertion compilation (debug builds only, zero release cost) (runtime_check! macro done; attribute form needs a proc-macro crate)
- [ ] proptest/quickcheck integration
- [ ] Counterexample replay for failed static proofs
- [ ] **Milestone: debug verification failures at runtime**

## Phase 6: Standard library

- [ ] Verified B-Tree
- [ ] Verified HashMap
- [ ] Verified Vec extensions
- [ ] Verified concurrency primitives (Mutex model; atomics later)
- [ ] I/O abstractions
- [ ] **Milestone: verified standard library**

## Phase 7: Filesystem integration

- [ ] Wire up `examples/filesystem` against `tpt-filesystem`
- [ ] Layer 1 types: block indices, sizes
- [ ] Layer 2 contracts on most functions
- [ ] Layer 3 proofs: B-Tree balance, CoW atomicity, transaction isolation
- [ ] **Milestone: filesystem has genuine mathematical guarantees**

## Phase 8: Self-verification

- [ ] Verify parts of the translation layer with tpt-proof
- [ ] Export proofs to Lean 4 / Coq for independent checking
- [ ] `proofs/kernel_soundness`
- [ ] **Milestone: framework self-verified to the extent possible**

## Later: extended Rust subset

- [ ] Phase 2 subset: closures, monomorphized generics, simple `unsafe` with proof obligations, mutexes/atomics
- [ ] Phase 3 subset: full safe Rust, complex `unsafe`, lock-free structures
- [ ] Concurrency logic (concurrent separation logic or session types)

## Ongoing

- [ ] Fuzzing and differential testing against Kani/Creusot
- [ ] Benchmarks (target: seconds for most verification)
- [ ] User docs, tutorials, error-message quality
- [ ] Success-criteria review (spec section 14)
