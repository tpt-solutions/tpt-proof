//! A first proof, end to end: prove a theorem with tactics, use an axiom, record
//! the theorems in the kernel, then print the dependency report and the Lean export.
//!
//! Run it with `cargo run -p tpt-proof --example first_proof`.

use tpt_proof::prelude::*;
use tpt_proof::report::dependency_report;
use tpt_proof::tactics::Proof;
use tpt_proof_export::{export, Lemma};
use tpt_proof_kernel::terms::{Sort, Term};

fn main() {
    let a = Prop::atom("A");
    let b = Prop::atom("B");
    let mut kernel = Kernel::new();

    // Theorem 1 uses no axioms: modus ponens, for every A and B. The tactics build
    // the proof, and the kernel checks it at `qed`.
    let modus_ponens = Prop::forall(
        "A",
        Prop::forall(
            "B",
            Prop::imp(
                Prop::imp(a.clone(), b.clone()),
                Prop::imp(a.clone(), b.clone()),
            ),
        ),
    );
    let mut proof = Proof::new(&kernel, modus_ponens.clone());
    proof.intro_forall("A").expect("the goal is for all A");
    proof.intro_forall("B").expect("the goal is for all B");
    proof.intro("f").expect("the goal is an implication");
    proof.intro("a").expect("the goal is an implication");
    proof.apply_hyp("f").expect("f takes an A and gives a B");
    proof.assumption().expect("a is an A");
    let theorem = proof.qed().expect("the kernel accepts the proof");
    println!("proved: {}", theorem.prop());
    let modus_ponens_term = ProofTerm::TyLam(
        "A".to_string(),
        Box::new(ProofTerm::TyLam(
            "B".to_string(),
            Box::new(ProofTerm::Lam(
                "f".to_string(),
                Prop::imp(a.clone(), b.clone()),
                Box::new(ProofTerm::Lam(
                    "a".to_string(),
                    a.clone(),
                    Box::new(ProofTerm::App(
                        Box::new(ProofTerm::Var("f".to_string())),
                        Box::new(ProofTerm::Var("a".to_string())),
                    )),
                )),
            )),
        )),
    );
    kernel
        .declare_theorem("modus_ponens", &modus_ponens_term, &modus_ponens)
        .expect("the term proves modus ponens");

    // Theorem 2 uses an axiom. The axiom says adding zero changes no integer. It is
    // closed, so the Lean export can state it. The proof instantiates it at 2.
    let x = Term::var("x");
    let add_zero = Prop::forall_sorted(
        "x",
        Sort::named("Int"),
        Prop::Eq(
            Term::Fun("+".to_string(), vec![x.clone(), Term::constant("0")]),
            x,
        ),
    );
    kernel
        .declare_axiom("add_zero", add_zero, "adding zero changes no integer")
        .expect("the axiom is closed");

    let two_plus_zero = Prop::Eq(
        Term::Fun(
            "+".to_string(),
            vec![Term::constant("2"), Term::constant("0")],
        ),
        Term::constant("2"),
    );
    let mut proof = Proof::new(&kernel, two_plus_zero.clone());
    proof
        .exact(ProofTerm::IndApp(
            Box::new(ProofTerm::Axiom("add_zero".to_string())),
            Term::constant("2"),
        ))
        .expect("add_zero at 2 is 2 + 0 = 2");
    proof.qed().expect("the kernel accepts the proof");
    let two_plus_zero_term = ProofTerm::IndApp(
        Box::new(ProofTerm::Axiom("add_zero".to_string())),
        Term::constant("2"),
    );
    kernel
        .declare_theorem("two_plus_zero", &two_plus_zero_term, &two_plus_zero)
        .expect("the term proves 2 + 0 = 2");

    println!();
    print!("{}", dependency_report(&kernel));

    // Lean checks every recorded proof independently of this kernel.
    let lemmas = vec![
        Lemma {
            name: "modus_ponens".to_string(),
            prop: modus_ponens,
            proof: modus_ponens_term,
        },
        Lemma {
            name: "two_plus_zero".to_string(),
            prop: two_plus_zero,
            proof: two_plus_zero_term,
        },
    ];
    match export(&kernel, &lemmas) {
        Ok(lean) => {
            println!();
            print!("{lean}");
        }
        Err(error) => eprintln!("could not export to Lean: {error}"),
    }
}
