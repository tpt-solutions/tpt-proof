//! Induction over natural numbers: define addition by recursion, then prove that
//! adding zero on the right changes nothing, for every natural number.
//!
//! Run it with `cargo run -p tpt-proof --example induction`.

use tpt_proof::prelude::*;
use tpt_proof::tactics::Proof;
use tpt_proof_kernel::terms::{Sort, Term};

fn nat() -> Sort {
    Sort::named("Nat")
}

fn zero() -> Term {
    Term::constant("zero")
}

fn succ(n: Term) -> Term {
    Term::app("succ", vec![n])
}

fn add(a: Term, b: Term) -> Term {
    Term::app("add", vec![a, b])
}

fn main() {
    let mut kernel = Kernel::new();

    // Nat is a free sort: zero, and succ applied to a Nat.
    kernel
        .declare_inductive("Nat", &[("zero", vec![]), ("succ", vec![nat()])])
        .expect("declares Nat");

    // add(zero, p0) = p0 and add(succ(a0), p0) = succ(add(a0, p0)). The kernel
    // generates the equations as axioms `add_zero` and `add_succ`.
    kernel
        .define_by_recursion_with_params(
            "add",
            &nat(),
            &[nat()],
            &nat(),
            &[
                ("zero", Term::var("p0")),
                ("succ", succ(add(Term::var("a0"), Term::var("p0")))),
            ],
        )
        .expect("add recurses on its first argument");

    // The claim: for every n, add(n, zero) = n. It needs induction, because the
    // equations only unfold addition on the first argument.
    let claim = Prop::forall_sorted(
        "n",
        nat(),
        Prop::Eq(add(Term::var("n"), zero()), Term::var("n")),
    );
    let mut proof = Proof::new(&kernel, claim.clone());
    proof.induct().expect("induct on n");
    println!("cases after induct: {}", proof.goals().len());

    // Zero case: add(zero, zero) = zero, which is add_zero at p0 := zero.
    proof
        .exact(ProofTerm::IndApp(
            Box::new(ProofTerm::Axiom("add_zero".to_string())),
            zero(),
        ))
        .expect("the zero case");

    // Successor case: the hypothesis is add(a0, zero) = a0. Unfold add on the left
    // with add_succ, then rewrite under succ with the hypothesis.
    proof.intro_individual("a0").expect("introduce a0");
    proof.intro("ih").expect("introduce the hypothesis");
    proof
        .exact(ProofTerm::Trans(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::IndApp(
                    Box::new(ProofTerm::Axiom("add_succ".to_string())),
                    zero(),
                )),
                Term::var("a0"),
            )),
            Box::new(ProofTerm::Cong(
                "succ".to_string(),
                vec![ProofTerm::Var("ih".to_string())],
            )),
        ))
        .expect("the successor case");

    let theorem = proof.qed().expect("the kernel accepts the induction");
    println!("proved: {}", theorem.prop());
    println!("uses axioms: {:?}", theorem.axioms());

    // The Lean export does not translate induction (see the limitations in
    // tpt-proof-export), so this example stops at the kernel check.
    println!("not exported to Lean: the export does not translate induction yet");
}
