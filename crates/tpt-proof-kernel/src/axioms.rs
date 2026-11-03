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
