//! Integer division and remainder, and integer arrays: the built-in operations
//! and their laws, checked through the kernel.

use tpt_proof_kernel::arith::INT;
use tpt_proof_kernel::axioms::{declare_arrays, declare_division, ARRAY};
use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::{Kernel, ProofTerm, Prop, Sort, Term};

fn c(n: &str) -> Term {
    Term::constant(n)
}

fn kernel() -> Kernel {
    let mut kernel = Kernel::new();
    declare_division(&mut kernel).expect("division axioms");
    declare_arrays(&mut kernel).expect("array axioms");
    kernel
        .declare_function_sorted("arr", Vec::new(), Sort::named(ARRAY))
        .expect("declare an array");
    kernel
}

fn ground(prop: Prop) -> ProofTerm {
    ProofTerm::Taut(Formula::Atom(prop))
}

#[test]
fn a_ground_remainder_is_evaluated_by_the_tautology_rule() {
    // 7 mod 3 = 1 and 7 div 3 = 2, with the Euclidean quotient and remainder.
    let kernel = kernel();
    let claim = Prop::Eq(Term::app("mod", vec![c("7"), c("3")]), c("1"));
    kernel
        .check_proof(&ground(claim.clone()), &claim)
        .expect("evaluated");
    let negative = Prop::Eq(Term::app("mod", vec![c("7"), c("0")]), c("1"));
    assert!(kernel
        .check_proof(&ground(negative.clone()), &negative)
        .is_err());
}

#[test]
fn a_negative_dividend_has_a_nonnegative_remainder() {
    // -7 = (-3) * 3 + 2 is Euclidean: the remainder is 2, not -1.
    let kernel = kernel();
    let minus_seven = Term::app("neg", vec![c("7")]);
    let claim = Prop::Eq(Term::app("mod", vec![minus_seven.clone(), c("3")]), c("2"));
    kernel
        .check_proof(&ground(claim.clone()), &claim)
        .expect("Euclidean remainder");
}

#[test]
fn the_remainder_is_below_its_divisor_by_axiom() {
    // mod_lt_divisor at x = 7, y = 3, with 0 < 3 by evaluation.
    let kernel = kernel();
    let claim = Prop::Pred(
        "<".to_string(),
        vec![Term::app("mod", vec![c("7"), c("3")]), c("3")],
    );
    let positive = Prop::Pred("<".to_string(), vec![c("0"), c("3")]);
    let proof = ProofTerm::App(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::Axiom("mod_lt_divisor".to_string())),
                c("7"),
            )),
            c("3"),
        )),
        Box::new(ground(positive)),
    );
    kernel
        .check_proof(&proof, &claim)
        .expect("the axiom instance");
}

#[test]
fn a_store_reads_back_its_value_by_axiom() {
    let kernel = kernel();
    let select = |a: Term, i: Term| Term::app("select", vec![a, i]);
    let store = |a: Term, i: Term, v: Term| Term::app("store", vec![a, i, v]);
    let claim = Prop::Eq(
        select(store(Term::constant("arr"), c("2"), c("5")), c("2")),
        c("5"),
    );
    let proof = ProofTerm::IndApp(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::Axiom("select_store_same".to_string())),
                Term::constant("arr"),
            )),
            c("2"),
        )),
        c("5"),
    );
    kernel
        .check_proof(&proof, &claim)
        .expect("select over store");
}

#[test]
fn a_store_leaves_other_indices_alone_by_axiom() {
    let kernel = kernel();
    let select = |a: Term, i: Term| Term::app("select", vec![a, i]);
    let store = |a: Term, i: Term, v: Term| Term::app("store", vec![a, i, v]);
    let claim = Prop::Eq(
        select(store(Term::constant("arr"), c("2"), c("5")), c("3")),
        select(Term::constant("arr"), c("3")),
    );
    let instance = ProofTerm::IndApp(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::IndApp(
                    Box::new(ProofTerm::Axiom("select_store_other".to_string())),
                    Term::constant("arr"),
                )),
                c("2"),
            )),
            c("3"),
        )),
        c("5"),
    );
    let proof = ProofTerm::App(
        Box::new(instance),
        Box::new(ProofTerm::Taut(Formula::Imp(
            Box::new(Formula::Atom(Prop::Eq(c("2"), c("3")))),
            Box::new(Formula::Const(false)),
        ))),
    );
    kernel
        .check_proof(&proof, &claim)
        .expect("the other element is unchanged");
}

#[test]
fn a_constant_array_holds_the_constant_everywhere() {
    let kernel = kernel();
    let claim = Prop::Eq(
        Term::app(
            "select",
            vec![Term::app("const_array", vec![c("7")]), c("1")],
        ),
        c("7"),
    );
    let proof = ProofTerm::IndApp(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::Axiom("select_const".to_string())),
            c("7"),
        )),
        c("1"),
    );
    kernel.check_proof(&proof, &claim).expect("constant array");
}

#[test]
fn a_wrong_read_is_refused() {
    let kernel = kernel();
    let claim = Prop::Eq(
        Term::app(
            "select",
            vec![
                Term::app("store", vec![Term::constant("arr"), c("2"), c("5")]),
                c("2"),
            ],
        ),
        c("6"),
    );
    let proof = ProofTerm::IndApp(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::Axiom("select_store_same".to_string())),
                Term::constant("arr"),
            )),
            c("2"),
        )),
        c("5"),
    );
    assert!(kernel.check_proof(&proof, &claim).is_err());
}

#[test]
fn declaring_the_laws_twice_is_a_no_op() {
    let mut kernel = kernel();
    declare_division(&mut kernel).expect("again");
    declare_arrays(&mut kernel).expect("again");
    assert!(kernel.sorts().any(|sort| sort == INT));
}
