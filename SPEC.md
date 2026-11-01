tpt-proof Design Specification
1. Purpose and Vision
tpt-proof is a layered, Rust-native formal verification framework designed to provide genuine mathematical guarantees for stateful, concurrent, data-structure-heavy Rust code — the exact class of software that existing verification tools handle poorly.
The Problem We Solve
Existing Rust verification tools force a false tradeoff:
Tool
Expressiveness
Usability
Kani
Limited (bounded)
Heavy (state explosion)
Creusot
Moderate
Heavy (separate Why3 ecosystem)
Liquid Rust
Low
Light (but can't prove hard things)
Aeneas
High
Very heavy (PhD-level proofs)
Prusti
Moderate
Complex setup, limited adoption
None of these can verify a real-world filesystem kernel. None are production-ready for the guarantees we need.
Our Answer
tpt-proof rejects the tradeoff. It provides:
Soundness — If it says code is correct, it is (mathematically guaranteed)
Expressiveness — Can prove structural invariants (B-Tree balance, CoW atomicity, transaction isolation)
Lightweight feedback — Seconds for 95% of verification; minutes/hours only for the hardest proofs
Rust-native — Specifications live in the code, in Rust syntax, not a separate language
Incremental — Verifies parts of a codebase; doesn't require whole-program verification
Composable — Verified libraries can be used without re-verification
Maintainable — Specifications don't become a burden as code evolves
What tpt-proof Is NOT
Not a model checker (no state-space exploration)
Not a type checker (Rust already has one)
Not a testing framework (it complements testing, doesn't replace it)
Not a general-purpose theorem prover (it's specialized for Rust programs)
Not a replacement for the Rust compiler (it runs alongside it)
2. Design Principles
Principle 1: The De Bruijn Criterion
The trusted computing base (TCB) must be small enough to audit by hand. Everything else is untrusted code that produces artifacts checked by the TCB.
Implication: The proof kernel is <5,000 lines of code. Tactics, SMT integration, translation — all untrusted. Only the kernel's verdict matters.
Principle 2: Progressive Disclosure of Complexity
Users should be able to get value at every level of engagement:
Level 0: Use refined types (zero proof burden)
Level 1: Write function contracts (automatic verification)
Level 2: Write loop invariants (mostly automatic)
Level 3: Write interactive proofs (manual but guided)
Most code needs only Levels 0-1. Level 3 is reserved for the hardest invariants.
Principle 3: Proof by Construction, Not by Search
Interactive proofs should feel like constructing a proof, not searching for one. The system suggests proof steps; the developer fills them in. This is more predictable and debuggable than SMT-style proof search.
Principle 4: Rust-First, Not Mathematics-First
Specifications should be written in Rust syntax, using Rust idioms. Users shouldn't need to learn a separate logic or proof language. When mathematical concepts are needed (e.g., invariants), they should be expressed as Rust traits and functions.
Principle 5: Fail Loudly, Never Silently
If verification can't complete, say so explicitly. Never fall back to "probably correct." Every verification result is one of:
Verified (proof checked by kernel)
Unverified (no proof attempted)
Failed (proof attempted, failed — with counterexample if possible)
Timeout (verification didn't complete in budget)
Principle 6: Compositional Verification
Verified components can be used without re-verification. A verified B-Tree library is verified once; users trust the specification, not the implementation. This is what makes scaling to large codebases possible.
3. The Four-Layer Architecture
tpt-proof is not one tool — it's a layered system where each layer handles a different class of verification problem at a different cost/expressiveness point.
Layer 1: Type-Level Specifications
What: Refinement types, ghost state, phantom types, and type-state patterns built into Rust's type system via macros and const evaluation.
Cost: Zero runtime cost. Zero proof burden. Compile-time only.
Handles:
Value bounds (index < length, size in range)
State machines (file handle: Open → Closed)
Unit correctness (blocks vs bytes vs sectors)
Structural invariants expressible in the type system
Example:

use tpt_proof::prelude::*;

#[refined(value < total_blocks)]
struct BlockIndex {
    value: usize,
    total_blocks: usize,
}

#[state_machine(Open, Writing, Closed)]
struct FileHandle {
    state: PhantomData<CurrentState>,
    // ...
}

impl FileHandle<Open> {
    fn write(self, data: &[u8]) -> FileHandle<Writing> { ... }
}

Implementation: Custom derive macros + const evaluation + limited SMT queries at compile time for simple bounds.
When to use: Always. This is the foundation. If an invariant can be expressed at Layer 1, it should be.
Layer 2: Contract-Based Verification
What: Function-level contracts (preconditions, postconditions, loop invariants) verified automatically via SMT (Z3) with proof-producing reflection.
Cost: Seconds per function. Automatic — no manual proof scripts.
Handles:
Function contracts (requires / ensures)
Loop invariants
Data structure invariants (B-Tree node balance, heap property)
Arithmetic overflow and underflow
Array bounds across function calls
Simple pointer validity
Example:

#[requires(tree.is_balanced())]
#[requires(key.is_valid())]
#[ensures(|result| result.is_ok() ==> tree.is_balanced())]
#[ensures(|result| result.is_ok() ==> tree.contains(key))]
fn insert(tree: &mut BTree, key: Key, value: Value) -> Result<()> {
    #[invariant(node.keys.len() <= MAX_KEYS)]
    #[invariant(node.keys.is_sorted())]
    for node in path.iter_mut() {
        // ...
    }
}

Implementation:
Translate Rust MIR to verification conditions (VCs)
Feed VCs to Z3
Z3 returns either a proof or a counterexample
Critical: Z3's output is not trusted directly. For each VC, we construct a proof term that the kernel checks. If Z3 can't produce a checkable proof term, the verification fails even if Z3 says "sat."
This is proof-producing reflection — the key to soundness with SMT.
When to use: For most function-level correctness. This is the workhorse layer.
Layer 3: Interactive Proofs
What: For invariants that SMT can't discharge automatically, a guided interactive proof mode. The developer constructs a proof step-by-step, with the system suggesting next steps and checking each one.
Cost: Minutes to hours per proof. Manual but guided.
Handles:
B-Tree rebalancing correctness
CoW transaction atomicity across crash scenarios
Transaction isolation properties
Complex concurrent protocols
Properties requiring induction
Example:

#[theorem]
fn cow_atomicity() {
    // Setup
    let fs: FileSystem = arbitrary();
    let tx: Transaction = arbitrary();
    
    // Assumptions
    assume(fs.is_consistent());
    assume(tx.is_valid_for(&fs));
    
    // Goal
    show("After any crash during tx.commit(), fs is consistent") {
        // The system suggests possible proof steps:
        // - Case split on crash point
        // - Apply lemma about CoW semantics
        // - Use invariant about superblock updates
        
        by {
            // Developer constructs proof using tactics
            case_split(crash_point());
            apply(lemma::cow_never_overwrites());
            apply(lemma::superblock_update_is_atomic());
            // Kernel checks each step
        }
    }
}

Implementation:
Custom proof DSL embedded in Rust via macros
Proof terms are checked by the kernel (Layer 3's core)
Tactics are untrusted code that suggest proof steps
Each step produces a proof term that the kernel validates
When to use: Only when Layer 2 can't handle it. These are the hard invariants that make the filesystem genuinely trustworthy.
Layer 4: Runtime Verification
What: Specifications compile to runtime assertions in debug builds. Catches bugs during development that static verification missed.
Cost: Runtime overhead in debug builds. Zero in release.
Handles:
Catching bugs in unverified code
Validating assumptions about third-party libraries
Debugging verification failures
Property-based testing integration
Example:

#[runtime_check(tree.is_balanced())]
fn debug_assert_balance(tree: &BTree) {
    // In debug builds, this actually checks balance
    // In release builds, this is a no-op
}

When to use: For code that can't be statically verified (FFI, legacy code, third-party libraries). Also invaluable for debugging verification failures.
4. The Kernel (The Heart of the System)
The kernel is the only trusted component of tpt-proof. If the kernel has a bug, every proof it accepts is suspect. Everything else — tactics, SMT integration, translation — is untrusted code that produces proof terms checked by the kernel.
Design Goals
Small — <5,000 lines of code, auditable by a domain expert in a few weeks
Sound — If the kernel accepts a proof, the theorem is true (modulo the trusted assumptions)
Simple — Based on a small, well-understood logical foundation
Efficient — Proof checking is fast (milliseconds per proof term)
Self-contained — No external dependencies that expand the TCB
The Logical Foundation
The kernel is based on a small LCF-style logical framework with:
A small core of primitive inference rules (assumption, implication intro/elim, universal intro/elim, etc.)
Inductive types for representing data structures
Recursive functions with termination checking
Propositional and first-order logic
A trusted notion of equality
This is similar in spirit to the Calculus of Constructions (what Coq is based on) but much smaller — we omit dependent types and other features that add complexity without helping for our use case.
The Proof Term Language
Proofs are represented as terms in a small AST:

enum ProofTerm {
    // Variables and constants
    Var(String),
    Const(String),
    
    // Lambda abstraction (proof of implication)
    Lam(String, Type, Box<ProofTerm>),
    
    // Application (modus ponens)
    App(Box<ProofTerm>, Box<ProofTerm>),
    
    // Universal quantification
    Forall(String, Type, Box<ProofTerm>),
    
    // Inductive type constructors
    Constr(String, Vec<ProofTerm>),
    
    // Pattern matching
    Match(Box<ProofTerm>, Vec<(Pattern, ProofTerm)>),
    
    // Axioms (trusted, explicitly declared)
    Axiom(String),
}

The Kernel's Job
The kernel exposes a small API:

impl Kernel {
    // Declare a new axiom (expands the TCB — use sparingly)
    fn declare_axiom(&mut self, name: &str, ty: Type) -> Result<()>;
    
    // Declare a new inductive type
    fn declare_inductive(&mut self, def: InductiveDef) -> Result<()>;
    
    // Define a new function (with termination proof)
    fn define_function(&mut self, name: &str, def: FunctionDef) -> Result<()>;
    
    // Check a proof term against a claimed type/theorem
    fn check_proof(&self, term: &ProofTerm, claimed_type: &Type) -> Result<Theorem>;
    
    // Assume a proposition (for interactive proofs — tracked explicitly)
    fn assume(&mut self, prop: Proposition) -> Result<Theorem>;
}

The kernel's check_proof function is the only way to produce a Theorem. If check_proof returns Ok(thm), the theorem is valid (modulo axioms). There is no other way to create a Theorem — the type is opaque, constructible only by the kernel.
The Trusted Axioms
The kernel starts with a small set of trusted axioms:
Logical axioms — The standard axioms of first-order logic
Equality axioms — Reflexivity, symmetry, transitivity, congruence
Arithmetic axioms — Peano axioms for natural numbers (bounded)
Rust semantics axioms — Axioms about Rust's operational semantics (ownership, borrowing, memory model) — these are the most controversial and must be carefully justified
The Rust semantics axioms are the biggest trust decision. We need to formalize:
What does it mean for Rust code to "execute correctly"?
How do we handle unsafe code?
How do we handle concurrency?
Initial approach: We axiomatize a safe subset of Rust. unsafe code is treated as an axiom that the caller must justify. Concurrency is handled via a separate concurrency logic (future work).
Proof Checking Algorithm
The kernel's proof checker is a simple recursive function:

fn check(ctx: &Context, term: &ProofTerm, expected: &Type) -> Result<()> {
    match term {
        ProofTerm::Var(name) => {
            let ty = ctx.lookup(name)?;
            ensure_eq(ty, expected)
        }
        ProofTerm::Lam(name, ty, body) => {
            // To check λx:T. body : T → U,
            // check body : U in context extended with x : T
            let expected_fn = expected.as_function()?;
            ensure_eq(ty, expected_fn.input);
            let mut ctx2 = ctx.clone();
            ctx2.extend(name, ty);
            check(&ctx2, body, expected_fn.output)
        }
        ProofTerm::App(f, x) => {
            // To check f x : U,
            // check f : T → U and x : T
            let f_ty = infer(ctx, f)?;
            let f_fn = f_ty.as_function()?;
            check(ctx, x, f_fn.input)?;
            ensure_eq(f_fn.output, expected)
        }
        // ... other cases
    }
}

This is straightforward, well-understood, and auditable. The complexity is in producing proof terms, not checking them.
Why This Design
Small TCB — The kernel is small enough to audit by hand
Clear trust boundary — Only the kernel's verdict matters
Sound by construction — The type system of the proof language ensures only valid proofs are accepted
Flexible — Tactics, SMT, and automation can be arbitrarily complex; they just need to produce valid proof terms
Well-understood — LCF-style kernels have 50+ years of successful use (HOL, Coq, Lean, etc.)
5. The Translation Layer
The translation layer converts Rust code into verification conditions (VCs) that can be checked by the kernel or fed to SMT.
The Challenge
Rust is complex:
Ownership and borrowing
Lifetimes
Traits and generics
Unsafe code
Concurrency
Macros
We can't translate all of Rust. We need to pick a verifiable subset and have a clear story for the rest.
The Verifiable Subset
Phase 1 (Initial):
Safe Rust only (no unsafe)
No closures (first pass)
No dynamic dispatch (no dyn Trait)
No raw pointers
No FFI
Limited concurrency (no shared mutable state without explicit synchronization)
Phase 2 (Extended):
Closures (with restrictions)
Generic code (monomorphized)
Simple unsafe blocks (with explicit proof obligations)
Basic concurrency primitives (mutexes, atomics)
Phase 3 (Full):
Full safe Rust
Complex unsafe abstractions
Advanced concurrency (lock-free data structures)
The Translation Pipeline

Rust source code
    ↓ (rustc)
MIR (Mid-level Intermediate Representation)
    ↓ (tpt-proof-mir)
Cleaned MIR (desugared, monomorphized, ownership resolved)
    ↓ (tpt-proof-vc)
Verification Conditions (logical formulas)
    ↓ (SMT or kernel)
Proof terms
    ↓ (kernel)
Theorems

Handling Ownership and Borrowing
Rust's ownership model is a huge advantage for verification:
No data races (by construction)
No aliasing bugs (by construction)
Clear lifetime semantics
We leverage this by:
Treating ownership as a linear logic resource
Borrowing as a temporary loan with clear return semantics
Lifetimes as proof obligations about scope
The translation converts Rust's ownership annotations into logical constraints that the kernel or SMT can reason about.
Handling unsafe
unsafe code is treated as an axiom that the caller must justify. When translating a function with unsafe blocks:
The unsafe block is replaced with an uninterpreted function
The caller must provide a proof that the unsafe usage is safe
The proof is checked by the kernel
This means unsafe code can be verified, but the burden of proof is explicit.
Handling Concurrency
Concurrency is the hardest part. Initial approach:
No shared mutable state without explicit synchronization
Mutexes modeled as resources with acquire/release protocols
Atomics modeled via a separate concurrency logic (future work)
Lock-free code is out of scope for Phase 1
We use a session types or concurrent separation logic approach to reason about concurrent protocols.
6. The Proof DSL
The proof DSL is embedded in Rust via macros. It should feel native to Rust, not like a separate language.
Contract Syntax (Layer 2)

#[requires(condition)]
#[ensures(|result| postcondition(result))]
#[ensures(|result| result.is_ok() ==> invariant_holds())]
fn function_name(args) -> ReturnType {
    #[invariant(loop_invariant)]
    for x in iter {
        // ...
    }
    
    #[assert(intermediate_assertion)]
    let y = compute();
    
    y
}

Theorem Syntax (Layer 3)

#[theorem]
fn theorem_name() {
    // Setup: introduce variables
    let x: Type = arbitrary();
    let y: Type = arbitrary();
    
    // Assumptions
    assume(premise_1());
    assume(premise_2());
    
    // Goal
    show("The statement to prove") {
        by {
            // Proof steps (tactics)
            step_1();
            step_2();
            // ...
        }
    }
}

Lemma Syntax

#[lemma]
fn lemma_name() {
    // Similar to theorem, but can be used by other proofs
}

Tactic Syntax
Tactics are functions that suggest proof steps:

fn case_split(prop: Proposition) -> ProofStep { ... }
fn apply(lemma: Theorem) -> ProofStep { ... }
fn induct(var: String) -> ProofStep { ... }
fn simplify() -> ProofStep { ... }

Tactics are untrusted — they suggest proof steps, but the kernel checks each step.
7. The Trust Model
What We Trust
The Rust compiler — We trust that it correctly implements Rust's semantics
The SMT solver (Z3) — We trust it for finding proofs, but not for verifying them
The kernel — We trust it because it's small and audited
The axioms — We trust them because they're explicitly declared and reviewed
What We Don't Trust
The translation layer — It could have bugs; the kernel checks its output
Tactics — They could suggest invalid steps; the kernel checks
SMT integration — Z3 could be wrong; we construct proof terms
User code — It could be buggy; verification catches it
The Trust Boundary

┌─────────────────────────────────────────────┐
│  Trusted (TCB)                              │
│  - Rust compiler                            │
│  - Kernel (<5K LOC, audited)                │
│  - Axioms (explicitly declared)             │
└─────────────────────────────────────────────┘
                    ↓ checks
┌─────────────────────────────────────────────┐
│  Untrusted                                  │
│  - Translation layer                        │
│  - Tactics                                  │
│  - SMT solver                               │
│  - User proofs                              │
└─────────────────────────────────────────────┘

Axiom Management
Axioms expand the TCB. We must be conservative:
Logical axioms — Standard, well-understood
Arithmetic axioms — Peano axioms, bounded
Rust semantics axioms — The most controversial; must be carefully justified and reviewed
User axioms — Allowed, but flagged as expanding the TCB
Every axiom is explicitly declared and documented. The system tracks which theorems depend on which axioms.
8. Self-Verification Strategy
The bootstrapping problem: How do we verify the verification framework?
Approach: Layered Self-Trust
The kernel is audited by hand. It's small enough (<5K LOC) that a domain expert can review it in a few weeks. We publish the audit report.
The translation layer is tested extensively. We use property-based testing, fuzzing, and comparison with other tools (Creusot, Kani) to build confidence.
Once the framework is working, we use it to verify parts of itself. The kernel can be partially verified by an earlier version of the framework. This is not circular — it's bootstrapping.
Critical proofs are exported to external provers. We can export proofs to Lean 4 or Coq for independent validation. If Lean agrees, we have high confidence.
The Bootstrap Sequence

Phase 1: Build kernel by hand, audit manually
Phase 2: Build translation layer, test extensively
Phase 3: Use tpt-proof to verify tpt-proof's translation layer
Phase 4: Export critical proofs to Lean/Coq for independent validation

This is how all serious verification frameworks bootstrap. It's not perfect, but it's the best we can do.
9. Relationship to tpt-filesystem
tpt-filesystem is the primary customer of tpt-proof. The two projects are co-designed:
How They Interact
tpt-filesystem drives tpt-proof development. Every feature of tpt-proof is motivated by a real verification need in the filesystem.
tpt-filesystem uses all four layers:
Layer 1: Refined types for block indices, sizes, etc.
Layer 2: Contracts for most functions
Layer 3: Interactive proofs for B-Tree balance, CoW atomicity, transaction isolation
Layer 4: Runtime checks for debugging
tpt-proof's standard library is built for tpt-filesystem. The verified B-Tree, HashMap, and concurrency primitives are first used in the filesystem.
The filesystem's correctness claims depend on tpt-proof. We can't claim "formally verified" until tpt-proof is trusted.
The Flywheel

tpt-proof (verification framework)
    ↓ provides guarantees
tpt-filesystem (proving ground)
    ↓ exposes real-world challenges
tpt-proof (improvements driven by needs)
    ↓
... (cycle continues)

10. Crate Structure

tpt-proof/
├── Cargo.toml                      # Workspace root
├── SPEC.md                         # This document
├── README.md
├── LICENSE-MIT
├── LICENSE-APACHE
│
├── crates/
│   ├── tpt-proof-kernel/           # The trusted proof kernel (Layer 3 core, <5K LOC, zero deps)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── terms.rs            # Proof term AST
│   │   │   ├── checker.rs          # Proof checker
│   │   │   └── axioms.rs           # Trusted axioms
│   │
│   ├── tpt-proof-core/             # Core types, refined types (Layer 1)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── refined.rs          # Refined type macros
│   │   │   ├── state_machine.rs    # Type-state patterns
│   │   │   └── units.rs            # Unit correctness
│   │
│   ├── tpt-proof-contract/         # Contract verification (Layer 2)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── contracts.rs        # requires/ensures/invariant
│   │   │   ├── vc.rs               # Verification condition generation
│   │   │   └── smt.rs              # Z3 integration (proof-producing)
│   │
│   ├── tpt-proof/                  # User-facing facade and prelude; proof DSL and tactics (Layer 3)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── dsl.rs              # Proof DSL macros
│   │   │   └── tactics.rs          # Tactic framework
│   │
│   ├── tpt-proof-runtime/          # Runtime verification (Layer 4)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   └── assertions.rs       # Runtime assertion compilation
│   │
│   ├── tpt-proof-mir/              # Rust MIR analysis (nightly only)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── translate.rs        # MIR → VCs
│   │   │   ├── ownership.rs        # Ownership analysis
│   │   │   └── concurrency.rs      # Concurrency analysis
│   │
│   └── tpt-proof-cli/              # Command-line interface
│       ├── src/
│       │   └── main.rs
│
├── kernel/                         # Audit surface: AUDIT.md; the kernel source lives in crates/tpt-proof-kernel
│   └── AUDIT.md                    # Audit status and reviewers
│
├── stdlib/                         # Verified standard library extensions
│   ├── collections/                # Verified B-Tree, HashMap, Vec
│   ├── sync/                       # Verified concurrency primitives
│   └── io/                         # Verified I/O abstractions
│
├── examples/
│   └── filesystem/                 # tpt-filesystem as the showcase
│
└── proofs/                         # Self-verification
    └── kernel_soundness/           # Proofs about the kernel itself

11. Licensing
Same philosophy as tpt-filesystem:
Core framework: dual-licensed MIT OR Apache-2.0 (Rust-standard dual license; copyright TPT Solutions)
No GPL dependencies. MIT and Apache-2.0 dependencies are allowed; anything else needs review (enforced by cargo-deny)
Linux kernel integration (if any): Isolated, GPLv2
The verification framework should be usable by anyone, for any purpose. This is critical for adoption.
12. Development Roadmap
Phase 1: Kernel Foundation
Build the LCF-style kernel
Implement proof term language and checker
Define trusted axioms
Hand-audit the kernel
Milestone: Kernel can check simple proofs
Phase 2: Layer 1 (Type-Level Specs)
Build refined types
Build type-state patterns
Build unit correctness
Milestone: Can write and check type-level specs
Phase 3: Layer 2 (Contracts)
Build MIR translation
Build VC generation
Integrate Z3 with proof-producing reflection
Build contract macros
Milestone: Can verify simple function contracts
Phase 4: Layer 3 (Interactive Proofs)
Build proof DSL
Build tactic framework
Build interactive proof mode
Milestone: Can write and check interactive proofs
Phase 5: Layer 4 (Runtime)
Build runtime assertion compilation
Integrate with property-based testing
Milestone: Can debug verification failures at runtime
Phase 6: Standard Library
Build verified B-Tree
Build verified HashMap
Build verified concurrency primitives
Milestone: Have a verified standard library
Phase 7: Filesystem Integration
Apply tpt-proof to tpt-filesystem
Verify B-Tree, CoW, transactions
Milestone: Filesystem has genuine mathematical guarantees
Phase 8: Self-Verification
Use tpt-proof to verify parts of itself
Export critical proofs to Lean/Coq
Milestone: Framework is self-verified (to the extent possible)
13. The Hard Problems (Being Honest)
Building tpt-proof is genuinely hard. Here are the problems we must confront:
1. The Bootstrapping Problem
How do we verify the verifier? Answer: Small kernel, manual audit, bootstrap gradually, export to external provers.
2. Rust's Type System Limitations
Rust's type system is powerful but not designed for verification. Answer: Extend via macros, accept limitations, focus on a verifiable subset.
3. SMT Solver Integration
Z3 is powerful but not infallible. Answer: Proof-producing reflection — Z3 suggests, kernel verifies.
4. Ownership + Verification
Rust's ownership model interacts complexly with verification. Answer: Treat ownership as linear logic, leverage it as an advantage.
5. Concurrency
Verifying concurrent code is fundamentally harder. Answer: Start with simple cases (mutexes), use session types or concurrent separation logic.
6. Performance
Verification must be fast enough for daily use. Answer: Aggressive caching, incremental verification, smart heuristics.
7. Adoption
Even if we build it, people need to use it. Answer: Excellent UX, helpful error messages, great documentation, tpt-filesystem as showcase.
14. Success Criteria
tpt-proof is successful if:
It can verify tpt-filesystem with genuine mathematical guarantees
It's usable by non-experts for common cases (Layers 1-2)
It's fast enough for daily use (seconds for most verification)
It's trusted by the community (small kernel, audited, transparent)
It contributes to Rust (upstreamable ideas, or at least influential)