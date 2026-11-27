//! Trusted axioms.
//!
//! Every axiom is declared with a proposition and a written justification.
//! The kernel tracks which theorems depend on which axioms (see
//! [`crate::Theorem::axioms`]). Adding an axiom to the kernel itself requires
//! a dedicated PR and an entry in `kernel/AUDIT.md`.
//!
//! A new kernel starts with no axioms: implication, quantifiers, equality, and
//! the tautology rule are primitive rules. The axioms here are the integer
//! laws that the tautology rule cannot decide, because they relate non-ground
//! atoms. [`declare_standard`] declares them. Each is true over the integers,
//! and each is listed in `kernel/AUDIT.md`.

use crate::arith::INT;
use crate::formula::FALSE;
use crate::terms::{Prop, Sort, Term};
use crate::{Kernel, Result};

/// A declared axiom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axiom {
    /// The name the axiom is referred to by.
    pub name: String,
    /// The proposition the axiom asserts.
    pub prop: Prop,
    /// Why the axiom is trusted.
    pub justification: String,
}

/// Declares the standard integer axioms in `kernel`. An axiom that is already
/// declared is skipped, so the call can be repeated.
pub fn declare_standard(kernel: &mut Kernel) -> Result<()> {
    for (name, prop, justification) in standard() {
        if kernel.axiom(name).is_none() {
            kernel.declare_axiom(name, prop, justification)?;
        }
    }
    Ok(())
}

/// The standard axioms as (name, proposition, justification) triples.
fn standard() -> Vec<(&'static str, Prop, &'static str)> {
    vec![
        (
            "le_cancel_right_fwd",
            for_all_int(&["x", "y", "z"], Prop::imp(le(add(x(), z()), add(y(), z())), le(x(), y()))),
            "Adding the same integer to both sides of an inequality preserves it, so it can be removed from both sides when the sides are integers.",
        ),
        (
            "le_cancel_right_bwd",
            for_all_int(&["x", "y", "z"], Prop::imp(le(x(), y()), le(add(x(), z()), add(y(), z())))),
            "Adding the same integer to both sides of an inequality preserves it over the integers.",
        ),
        (
            "lt_def_fwd",
            for_all_int(
                &["x", "y"],
                Prop::imp(lt(x(), y()), Prop::imp(le(y(), x()), falsum())),
            ),
            "Over the integers, x < y and y <= x cannot both hold, which is the definition of < by <=.",
        ),
        (
            "lt_def_bwd",
            for_all_int(
                &["x", "y"],
                Prop::imp(Prop::imp(le(y(), x()), falsum()), lt(x(), y())),
            ),
            "Over the integers, if not y <= x then x < y, because the integers are totally ordered.",
        ),
        (
            "add_cancel_left_fwd",
            for_all_int(
                &["x", "y", "z"],
                Prop::imp(Prop::Eq(add(z(), x()), add(z(), y())), Prop::Eq(x(), y())),
            ),
            "Adding the same integer on the left of both sides of an equation preserves it, so it can be removed from both sides when the sides are integers.",
        ),
        (
            "add_cancel_left_bwd",
            for_all_int(
                &["x", "y", "z"],
                Prop::imp(Prop::Eq(x(), y()), Prop::Eq(add(z(), x()), add(z(), y()))),
            ),
            "Adding the same integer on the left of two equal integers gives equal sums.",
        ),
        (
            "add_comm",
            for_all_int(&["x", "y"], Prop::Eq(add(x(), y()), add(y(), x()))),
            "Integer addition is commutative.",
        ),
        (
            "add_zero",
            for_all_int(&["x"], Prop::Eq(add(x(), Term::constant("0")), x())),
            "Zero is the additive identity for integers.",
        ),
        (
            "le_antisymm",
            for_all_int(
                &["x", "y"],
                Prop::imp(le(x(), y()), Prop::imp(le(y(), x()), Prop::Eq(x(), y()))),
            ),
            "The order on the integers is antisymmetric: if x <= y and y <= x then x = y. Each side is an integer, so the equation holds in both directions of the order.",
        ),
        (
            "ite_true",
            for_all_int(
                &["x", "y"],
                Prop::Eq(
                    Term::Ite(
                        Box::new(Prop::imp(falsum(), falsum())),
                        Box::new(x()),
                        Box::new(y()),
                    ),
                    x(),
                ),
            ),
            "A conditional whose condition is true, the constant true, is its then-branch. This is the meaning of the conditional term.",
        ),
        (
            "ite_false",
            for_all_int(
                &["x", "y"],
                Prop::Eq(
                    Term::Ite(Box::new(falsum()), Box::new(x()), Box::new(y())),
                    y(),
                ),
            ),
            "A conditional whose condition is false, the constant false, is its else-branch. This is the meaning of the conditional term.",
        ),
    ]
}

fn x() -> Term {
    Term::var("x")
}

fn y() -> Term {
    Term::var("y")
}

fn z() -> Term {
    Term::var("z")
}

fn add(a: Term, b: Term) -> Term {
    Term::app("+", vec![a, b])
}

fn le(a: Term, b: Term) -> Prop {
    Prop::Pred("<=".to_string(), vec![a, b])
}

fn lt(a: Term, b: Term) -> Prop {
    Prop::Pred("<".to_string(), vec![a, b])
}

fn falsum() -> Prop {
    Prop::atom(FALSE)
}

/// Universally quantifies `body` over each of `names`, all of sort `Int`.
fn for_all_int(names: &[&str], body: Prop) -> Prop {
    names.iter().rev().fold(body, |acc, name| {
        Prop::forall_sorted(name, Sort::named(INT), acc)
    })
}

/// The name of the sort of integer arrays.
pub const ARRAY: &str = "IntArray";

/// Declares integer division and remainder. `div` and `mod` are built-in
/// operations (see [`crate::Kernel::new`]); their laws are the axioms here,
/// which hold for a positive divisor. Declaring them again is a no-op.
pub fn declare_division(kernel: &mut Kernel) -> Result<()> {
    for (name, prop, justification) in division() {
        if kernel.axiom(name).is_none() {
            kernel.declare_axiom(name, prop, justification)?;
        }
    }
    Ok(())
}

fn division() -> Vec<(&'static str, Prop, &'static str)> {
    let positive = |body: Prop| Prop::imp(lt(zero(), y()), body);
    vec![
        (
            "div_mod_euclid",
            for_all_int(
                &["x", "y"],
                positive(Prop::Eq(
                    x(),
                    add(mul(y(), div(x(), y())), modulo(x(), y())),
                )),
            ),
            "Euclidean division: for a positive divisor, the dividend is the divisor times the quotient plus the remainder.",
        ),
        (
            "mod_nonneg",
            for_all_int(&["x", "y"], positive(le(zero(), modulo(x(), y())))),
            "The Euclidean remainder of a positive divisor is not negative.",
        ),
        (
            "mod_lt_divisor",
            for_all_int(&["x", "y"], positive(lt(modulo(x(), y()), y()))),
            "The Euclidean remainder of a positive divisor is less than the divisor.",
        ),
    ]
}

/// Declares integer arrays: the sort [`ARRAY`], the functions `select`, `store`
/// and `const_array`, and their laws. Declaring them again is a no-op.
pub fn declare_arrays(kernel: &mut Kernel) -> Result<()> {
    let array = || Sort::named(ARRAY);
    let int = || Sort::named(INT);
    if !kernel.sorts().any(|sort| sort == ARRAY) {
        kernel.declare_sort(ARRAY)?;
    }
    if kernel.function_signature("select").is_none() {
        kernel.declare_function_sorted("select", vec![array(), int()], int())?;
        kernel.declare_function_sorted("store", vec![array(), int(), int()], array())?;
        kernel.declare_function_sorted("const_array", vec![int()], array())?;
    }
    for (name, prop, justification) in array_laws() {
        if kernel.axiom(name).is_none() {
            kernel.declare_axiom(name, prop, justification)?;
        }
    }
    Ok(())
}

fn array_laws() -> Vec<(&'static str, Prop, &'static str)> {
    let array = || Sort::named(ARRAY);
    let int = || Sort::named(INT);
    let a = || Term::var("a");
    let i = || Term::var("i");
    let j = || Term::var("j");
    let v = || Term::var("v");
    let select = |array: Term, index: Term| Term::app("select", vec![array, index]);
    let store =
        |array: Term, index: Term, value: Term| Term::app("store", vec![array, index, value]);
    vec![
        (
            "select_store_same",
            quantify(
                &[("a", array()), ("i", int()), ("v", int())],
                Prop::Eq(select(store(a(), i(), v()), i()), v()),
            ),
            "Reading an array at the index it was last written at returns the written value. This is the defining law of the store.",
        ),
        (
            "select_store_other",
            quantify(
                &[("a", array()), ("i", int()), ("j", int()), ("v", int())],
                Prop::imp(
                    Prop::imp(Prop::Eq(i(), j()), falsum()),
                    Prop::Eq(select(store(a(), i(), v()), j()), select(a(), j())),
                ),
            ),
            "Writing at one index does not change the element at a different index.",
        ),
        (
            "select_const",
            quantify(
                &[("v", int()), ("i", int())],
                Prop::Eq(select(Term::app("const_array", vec![v()]), i()), v()),
            ),
            "Every element of a constant array holds the constant.",
        ),
    ]
}

fn zero() -> Term {
    Term::constant("0")
}

fn mul(a: Term, b: Term) -> Term {
    Term::app("*", vec![a, b])
}

fn div(a: Term, b: Term) -> Term {
    Term::app("div", vec![a, b])
}

fn modulo(a: Term, b: Term) -> Term {
    Term::app("mod", vec![a, b])
}

/// Universally quantifies `body` over each binder, in order, with its sort.
fn quantify(binders: &[(&str, Sort)], body: Prop) -> Prop {
    binders.iter().rev().fold(body, |acc, (name, sort)| {
        Prop::forall_sorted(name, sort.clone(), acc)
    })
}
