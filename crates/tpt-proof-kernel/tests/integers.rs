//! The tautology rule (`ProofTerm::Taut`), the built-in integers, and the
//! standard integer axioms.

// Kernel errors carry whole propositions, so the error type is large. See the
// kernel crate root, which allows the same lint for the same reason.
#![allow(clippy::result_large_err)]

use tpt_proof_kernel::arith::INT;
use tpt_proof_kernel::axioms::declare_standard;
use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::terms::{ProofTerm, Prop, Sort, Term};
use tpt_proof_kernel::{Kernel, KernelError};

fn atom(name: &str) -> Formula {
    Formula::Atom(Prop::atom(name))
}

fn num(n: i64) -> Term {
    Term::constant(&n.to_string())
}

fn le(a: Term, b: Term) -> Formula {
    Formula::Atom(Prop::Pred("<=".to_string(), vec![a, b]))
}

fn taut(formula: Formula) -> ProofTerm {
    ProofTerm::Taut(formula)
}

fn check(kernel: &Kernel, formula: Formula) -> Result<(), KernelError> {
    let claimed = formula.encode();
    kernel.check_proof(&taut(formula), &claimed).map(|_| ())
}

#[test]
fn accepts_a_propositional_tautology() {
    let kernel = Kernel::new();
    let excluded_middle = Formula::Or(vec![atom("a"), Formula::Not(Box::new(atom("a")))]);
    assert!(check(&kernel, excluded_middle).is_ok());
    let double_negation = Formula::Imp(
        Box::new(Formula::Not(Box::new(Formula::Not(Box::new(atom("a")))))),
        Box::new(atom("a")),
    );
    assert!(check(&kernel, double_negation).is_ok());
}

#[test]
fn rejects_a_formula_that_a_valuation_falsifies() {
    let kernel = Kernel::new();
    let formula = Formula::Imp(Box::new(atom("a")), Box::new(atom("b")));
    assert!(matches!(
        check(&kernel, formula),
        Err(KernelError::NotATautology(_))
    ));
}

#[test]
fn an_iff_encodes_as_two_implications_and_is_checked_as_one() {
    let kernel = Kernel::new();
    let iff = Formula::Iff(Box::new(atom("a")), Box::new(atom("a")));
    assert!(check(&kernel, iff).is_ok());
    // Claiming a different proposition than the formula encodes is refused.
    let formula = Formula::Iff(Box::new(atom("a")), Box::new(atom("b")));
    let wrong = Prop::atom("a");
    assert!(kernel.check_proof(&taut(formula), &wrong).is_err());
}

#[test]
fn ground_atoms_are_evaluated_with_integer_meaning() {
    let kernel = Kernel::new();
    assert!(check(&kernel, le(num(2), num(3))).is_ok());
    assert!(matches!(
        check(&kernel, le(num(3), num(2))),
        Err(KernelError::NotATautology(_))
    ));
    // 2 + 3 = 5, and negative numerals are negations.
    let sum = Term::app("+", vec![num(2), num(3)]);
    let eq = Formula::Atom(Prop::Eq(sum, num(5)));
    assert!(check(&kernel, eq).is_ok());
    let negative = Term::app("neg", vec![num(7)]);
    let less = Formula::Atom(Prop::Pred("<".to_string(), vec![negative, num(0)]));
    assert!(check(&kernel, less).is_ok());
}

#[test]
fn the_false_atom_is_the_constant_false() {
    let kernel = Kernel::new();
    assert!(check(&kernel, atom("false")).is_err());
    let not_false = Formula::Not(Box::new(atom("false")));
    assert!(check(&kernel, not_false).is_ok());
}

#[test]
fn non_ground_arithmetic_atoms_are_letters() {
    let mut kernel = Kernel::new();
    kernel
        .declare_function_sorted("x", vec![], Sort::named(INT))
        .unwrap();
    kernel
        .declare_function_sorted("y", vec![], Sort::named(INT))
        .unwrap();
    let x_le_y = le(Term::constant("x"), Term::constant("y"));
    let excluded_middle = Formula::Or(vec![x_le_y.clone(), Formula::Not(Box::new(x_le_y.clone()))]);
    assert!(check(&kernel, excluded_middle).is_ok());
    // Without the arithmetic meaning, x <= y is not decided, so it is not a tautology.
    assert!(check(&kernel, x_le_y).is_err());
}

#[test]
fn numerals_must_be_canonical() {
    let mut kernel = Kernel::new();
    assert!(matches!(
        kernel.declare_function("3", 0),
        Err(KernelError::ReservedSymbol(_))
    ));
    // `07` is not a numeral, so it is an unknown symbol, not the integer seven.
    let claim = Formula::Atom(Prop::Eq(Term::constant("07"), num(7))).encode();
    assert!(kernel
        .check_proof(
            &taut(Formula::Atom(Prop::Eq(Term::constant("07"), num(7)))),
            &claim
        )
        .is_err());
}

#[test]
fn built_in_operations_cannot_be_redeclared() {
    let mut kernel = Kernel::new();
    assert!(kernel.declare_function("+", 2).is_err());
    assert!(kernel.declare_predicate("<=", 2).is_err());
    assert!(kernel.declare_sort(INT).is_err());
}

#[test]
fn a_tautology_with_too_many_letters_is_refused() {
    let kernel = Kernel::new();
    let letters: Vec<Formula> = (0..17).map(|i| atom(&format!("p{i}"))).collect();
    let formula = Formula::Or(letters);
    assert!(matches!(
        check(&kernel, formula),
        Err(KernelError::TooManyLetters(17))
    ));
}

#[test]
fn standard_axioms_are_declared_once_and_are_idempotent() {
    let mut kernel = Kernel::new();
    declare_standard(&mut kernel).unwrap();
    declare_standard(&mut kernel).unwrap();
    assert_eq!(kernel.axioms().count(), 8);
}

#[test]
fn an_instance_of_a_standard_axiom_is_a_checked_proof() {
    let mut kernel = Kernel::new();
    declare_standard(&mut kernel).unwrap();
    for name in ["a", "b", "c"] {
        kernel
            .declare_function_sorted(name, vec![], Sort::named(INT))
            .unwrap();
    }
    // le_cancel_right_fwd: forall x y z. x + z <= y + z -> x <= y, at a, b, c.
    let instance = ProofTerm::IndApp(
        Box::new(ProofTerm::IndApp(
            Box::new(ProofTerm::IndApp(
                Box::new(ProofTerm::Axiom("le_cancel_right_fwd".to_string())),
                Term::constant("a"),
            )),
            Term::constant("b"),
        )),
        Term::constant("c"),
    );
    let add = |l: Term, r: Term| Term::app("+", vec![l, r]);
    let claimed = Prop::imp(
        Prop::Pred(
            "<=".to_string(),
            vec![
                add(Term::constant("a"), Term::constant("c")),
                add(Term::constant("b"), Term::constant("c")),
            ],
        ),
        Prop::Pred(
            "<=".to_string(),
            vec![Term::constant("a"), Term::constant("b")],
        ),
    );
    let theorem = kernel.check_proof(&instance, &claimed).unwrap();
    assert!(theorem.axioms().contains("le_cancel_right_fwd"));

    // Swapping the instantiation is refused: the claim no longer matches.
    let wrong = Prop::imp(
        Prop::Pred(
            "<=".to_string(),
            vec![
                add(Term::constant("a"), Term::constant("c")),
                add(Term::constant("b"), Term::constant("c")),
            ],
        ),
        Prop::Pred(
            "<=".to_string(),
            vec![Term::constant("b"), Term::constant("a")],
        ),
    );
    assert!(kernel.check_proof(&instance, &wrong).is_err());
}
