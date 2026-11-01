//! Kernel checking time, measured with the standard library clock: a chain of
//! modus ponens steps of growing length, and a deeply nested proof of identity.
//! Run with `cargo bench -p tpt-proof-kernel`.

use std::time::Instant;

use tpt_proof_kernel::{Kernel, ProofTerm, Prop};

/// Proves `A_n` from `A_0` and implications `A_i -> A_{i+1}`, by applying each in turn.
fn chain(length: usize) -> (Kernel, ProofTerm, Prop) {
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("start", Prop::atom("A0"), "benchmark")
        .expect("declare start");
    for i in 0..length {
        let step = Prop::imp(
            Prop::atom(&format!("A{i}")),
            Prop::atom(&format!("A{}", i + 1)),
        );
        kernel
            .declare_axiom(&format!("step{i}"), step, "benchmark")
            .expect("declare step");
    }
    let mut term = ProofTerm::Axiom("start".to_string());
    for i in 0..length {
        term = ProofTerm::App(
            Box::new(ProofTerm::Axiom(format!("step{i}"))),
            Box::new(term),
        );
    }
    (kernel, term, Prop::atom(&format!("A{length}")))
}

/// Proves `A -> A` by `n` nested identity functions applied to the hypothesis.
fn nested_identity(depth: usize) -> (Kernel, ProofTerm, Prop) {
    let kernel = Kernel::new();
    let mut term = ProofTerm::Var("x".to_string());
    for _ in 0..depth {
        term = ProofTerm::App(
            Box::new(ProofTerm::Lam(
                "y".to_string(),
                Prop::atom("A"),
                Box::new(ProofTerm::Var("y".to_string())),
            )),
            Box::new(term),
        );
    }
    let claim = Prop::imp(Prop::atom("A"), Prop::atom("A"));
    (
        kernel,
        ProofTerm::Lam("x".to_string(), Prop::atom("A"), Box::new(term)),
        claim,
    )
}

fn time<F: FnOnce() -> bool>(label: &str, size: usize, run: F) {
    let start = Instant::now();
    let ok = run();
    let elapsed = start.elapsed();
    println!("{label:<22} size {size:>5}  checked {ok}  {elapsed:?}");
}

fn main() {
    // The checker recurses once per level of proof nesting, so sizes are capped below the
    // default stack limit. See docs/benchmarks.md, "Stack depth".
    for length in [10, 50, 100] {
        let (kernel, term, claim) = chain(length);
        time("modus ponens chain", length, || {
            kernel.check_proof(&term, &claim).is_ok()
        });
    }
    for depth in [10, 50, 100] {
        let (kernel, term, claim) = nested_identity(depth);
        time("nested identity", depth, || {
            kernel.check_proof(&term, &claim).is_ok()
        });
    }
}
