//! Boolean formulas and their encoding into propositions.
//!
//! [`Prop`] has implication and quantifiers only. The other connectives are
//! encoded in second-order logic, so a formula can be checked by the
//! tautology rule ([`crate::ProofTerm::Taut`]) and then used as an ordinary
//! proposition:
//!
//! - `not a` is `a -> false`;
//! - `a and b` is `forall r. (a -> b -> r) -> r`, and `and` of no formulas is `true`;
//! - `a or b` is `forall r. (a -> r) -> (b -> r) -> r`, and `or` of no formulas is `false`;
//! - `a iff b` is `(a -> b) and (b -> a)`;
//! - `true` is `false -> false`.
//!
//! The encodings are classically equivalent to the connectives they stand for,
//! which is the only fact the tautology rule relies on.

use crate::terms::Prop;

/// The constant false proposition. It is an atom with this name, and the
/// tautology rule evaluates it as the constant false, never as a letter.
pub const FALSE: &str = "false";

/// The propositional variable bound by the encodings of `and` and `or`.
const BINDER: &str = "#r";

/// A Boolean formula over propositions. Its atoms are arbitrary propositions.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    /// An atomic proposition.
    Atom(Prop),
    /// The constant true or false.
    Const(bool),
    /// Negation.
    Not(Box<Formula>),
    /// Conjunction of any number of formulas.
    And(Vec<Formula>),
    /// Disjunction of any number of formulas.
    Or(Vec<Formula>),
    /// Implication.
    Imp(Box<Formula>, Box<Formula>),
    /// Equivalence.
    Iff(Box<Formula>, Box<Formula>),
}

impl Formula {
    /// The proposition this formula stands for, using the encodings in the
    /// module documentation.
    pub fn encode(&self) -> Prop {
        match self {
            Formula::Atom(prop) => prop.clone(),
            Formula::Const(true) => Prop::imp(Prop::atom(FALSE), Prop::atom(FALSE)),
            Formula::Const(false) => Prop::atom(FALSE),
            Formula::Not(a) => Prop::imp(a.encode(), Prop::atom(FALSE)),
            Formula::And(items) => {
                if items.is_empty() {
                    return Formula::Const(true).encode();
                }
                let items: Vec<Prop> = items.iter().map(Formula::encode).collect();
                encode_and(items)
            }
            Formula::Or(items) => {
                if items.is_empty() {
                    return Formula::Const(false).encode();
                }
                let items: Vec<Prop> = items.iter().map(Formula::encode).collect();
                encode_or(items)
            }
            Formula::Imp(a, b) => Prop::imp(a.encode(), b.encode()),
            Formula::Iff(a, b) => encode_and(vec![
                Prop::imp(a.encode(), b.encode()),
                Prop::imp(b.encode(), a.encode()),
            ]),
        }
    }

    /// Adds every atom of this formula to `out`, in order of occurrence.
    pub(crate) fn atoms<'a>(&'a self, out: &mut Vec<&'a Prop>) {
        match self {
            Formula::Atom(prop) => out.push(prop),
            Formula::Const(_) => {}
            Formula::Not(a) => a.atoms(out),
            Formula::And(items) | Formula::Or(items) => {
                items.iter().for_each(|item| item.atoms(out))
            }
            Formula::Imp(a, b) | Formula::Iff(a, b) => {
                a.atoms(out);
                b.atoms(out);
            }
        }
    }
}

/// `forall r. (items -> r) -> r`, where `items` is `a1 -> ... -> an -> r`.
fn encode_and(items: Vec<Prop>) -> Prop {
    let r = Prop::atom(BINDER);
    let body = items
        .into_iter()
        .rev()
        .fold(r.clone(), |acc, item| Prop::imp(item, acc));
    Prop::forall(BINDER, Prop::imp(body, r))
}

/// `forall r. (a1 -> r) -> ... -> (an -> r) -> r`.
fn encode_or(items: Vec<Prop>) -> Prop {
    let r = Prop::atom(BINDER);
    let body = items.into_iter().rev().fold(r.clone(), |acc, item| {
        Prop::imp(Prop::imp(item, r.clone()), acc)
    });
    Prop::forall(BINDER, body)
}
