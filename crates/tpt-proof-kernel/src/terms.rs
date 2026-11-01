//! Propositions, terms, and the proof term language.
//!
//! The logic is a second-order propositional logic (System F restricted to
//! propositions) with equality between ground first-order terms. Propositions
//! are atoms, implication, quantification over propositional variables, and
//! equalities `t = s`. A proof of `p` is a term of type `p` (Curry-Howard).
//!
//! Terms are applications of uninterpreted function symbols, so `Fun("a", [])`
//! is an individual constant. Quantification over individuals, inductive types,
//! and pattern matching from SPEC.md §4 are not implemented yet; see
//! `kernel/AUDIT.md`.

use std::fmt;

/// A ground first-order term: an uninterpreted function symbol applied to
/// arguments. A symbol with no arguments is a constant.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Term {
    /// The function symbol.
    pub symbol: String,
    /// The arguments.
    pub args: Vec<Term>,
}

impl Term {
    /// Builds an application of `symbol` to `args`.
    pub fn app(symbol: &str, args: Vec<Term>) -> Term {
        Term {
            symbol: symbol.to_string(),
            args,
        }
    }

    /// Builds a constant, an application to no arguments.
    pub fn constant(symbol: &str) -> Term {
        Term::app(symbol, Vec::new())
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.args.is_empty() {
            return write!(f, "{}", self.symbol);
        }
        let args: Vec<String> = self.args.iter().map(|a| a.to_string()).collect();
        write!(f, "{}({})", self.symbol, args.join(", "))
    }
}

/// A proposition.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Prop {
    /// An atomic proposition or propositional variable, such as `A`.
    Atom(String),
    /// Implication `A -> B`.
    Imp(Box<Prop>, Box<Prop>),
    /// Universal quantification over a propositional variable: `forall p. A`.
    Forall(String, Box<Prop>),
    /// Equality of two ground terms.
    Eq(Term, Term),
}

impl Prop {
    /// Builds an atomic proposition.
    pub fn atom(name: &str) -> Prop {
        Prop::Atom(name.to_string())
    }

    /// Builds the implication `a -> b`.
    pub fn imp(a: Prop, b: Prop) -> Prop {
        Prop::Imp(Box::new(a), Box::new(b))
    }

    /// Builds the quantified proposition `forall name. body`.
    pub fn forall(name: &str, body: Prop) -> Prop {
        Prop::Forall(name.to_string(), Box::new(body))
    }

    /// Whether `name` occurs free in this proposition.
    pub fn has_free(&self, name: &str) -> bool {
        match self {
            Prop::Atom(atom) => atom == name,
            Prop::Imp(a, b) => a.has_free(name) || b.has_free(name),
            Prop::Forall(bound, body) => bound != name && body.has_free(name),
            Prop::Eq(_, _) => false,
        }
    }

    /// Every free variable name in this proposition.
    pub(crate) fn free_vars(&self, out: &mut Vec<String>) {
        match self {
            Prop::Atom(atom) => {
                if !out.contains(atom) {
                    out.push(atom.clone());
                }
            }
            Prop::Imp(a, b) => {
                a.free_vars(out);
                b.free_vars(out);
            }
            Prop::Forall(bound, body) => {
                let mut inner = Vec::new();
                body.free_vars(&mut inner);
                for name in inner {
                    if name != *bound && !out.contains(&name) {
                        out.push(name);
                    }
                }
            }
            Prop::Eq(_, _) => {}
        }
    }

    /// Whether two propositions are equal up to renaming of bound variables.
    pub fn alpha_eq(&self, other: &Prop) -> bool {
        alpha_eq(self, other)
    }

    /// Substitutes `replacement` for the free variable `name`, renaming bound
    /// variables where needed so that no free variable is captured.
    pub fn substitute(&self, name: &str, replacement: &Prop) -> Prop {
        match self {
            Prop::Atom(atom) if atom == name => replacement.clone(),
            Prop::Atom(_) => self.clone(),
            Prop::Imp(a, b) => Prop::imp(
                a.substitute(name, replacement),
                b.substitute(name, replacement),
            ),
            Prop::Forall(bound, body) if bound == name => self.clone(),
            Prop::Forall(bound, body) => {
                let mut replacement_vars = Vec::new();
                replacement.free_vars(&mut replacement_vars);
                if replacement_vars.contains(bound) {
                    // Rename the binder to a name that is free in neither side.
                    let mut fresh = format!("{bound}'");
                    let mut body_vars = Vec::new();
                    body.free_vars(&mut body_vars);
                    while replacement_vars.contains(&fresh) || body_vars.contains(&fresh) {
                        fresh.push('\'');
                    }
                    let renamed = body.substitute(bound, &Prop::Atom(fresh.clone()));
                    Prop::forall(&fresh, renamed.substitute(name, replacement))
                } else {
                    Prop::forall(bound, body.substitute(name, replacement))
                }
            }
            Prop::Eq(_, _) => self.clone(),
        }
    }
}

/// Equality up to renaming of bound propositional variables.
pub(crate) fn alpha_eq(a: &Prop, b: &Prop) -> bool {
    alpha_eq_in(a, b, &mut Vec::new())
}

fn alpha_eq_in(a: &Prop, b: &Prop, scope: &mut Vec<(String, String)>) -> bool {
    match (a, b) {
        (Prop::Atom(x), Prop::Atom(y)) => {
            let left = scope.iter().rposition(|(bound, _)| bound == x);
            let right = scope.iter().rposition(|(_, bound)| bound == y);
            match (left, right) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false,
            }
        }
        (Prop::Imp(a1, b1), Prop::Imp(a2, b2)) => {
            alpha_eq_in(a1, a2, scope) && alpha_eq_in(b1, b2, scope)
        }
        (Prop::Forall(x, body1), Prop::Forall(y, body2)) => {
            scope.push((x.clone(), y.clone()));
            let equal = alpha_eq_in(body1, body2, scope);
            scope.pop();
            equal
        }
        (Prop::Eq(l1, r1), Prop::Eq(l2, r2)) => l1 == l2 && r1 == r2,
        _ => false,
    }
}

impl fmt::Display for Prop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prop::Atom(name) => write!(f, "{name}"),
            Prop::Imp(a, b) => write!(f, "({a} -> {b})"),
            Prop::Forall(name, body) => write!(f, "(forall {name}. {body})"),
            Prop::Eq(l, r) => write!(f, "({l} = {r})"),
        }
    }
}

/// A proof term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofTerm {
    /// A variable bound by an enclosing [`ProofTerm::Lam`].
    Var(String),
    /// A previously checked theorem, by name.
    Const(String),
    /// A declared axiom, by name. Its use is recorded as a dependency.
    Axiom(String),
    /// Implication introduction: `λ name : prop. body`.
    Lam(String, Prop, Box<ProofTerm>),
    /// Implication elimination (modus ponens): `function argument`.
    App(Box<ProofTerm>, Box<ProofTerm>),
    /// Universal introduction: `Λ name. body`, proving `forall name. A`.
    TyLam(String, Box<ProofTerm>),
    /// Universal elimination: instantiates `function` at the proposition `argument`.
    TyApp(Box<ProofTerm>, Prop),
    /// Reflexivity: proves `t = t`.
    Refl(Term),
    /// Symmetry: from a proof of `t = s`, proves `s = t`.
    Sym(Box<ProofTerm>),
    /// Transitivity: from `t = s` and `s = u`, proves `t = u`.
    Trans(Box<ProofTerm>, Box<ProofTerm>),
    /// Congruence: from `t_i = s_i` for each argument, proves
    /// `f(t_1, ..) = f(s_1, ..)`. Each argument proof must prove an equality.
    Cong(String, Vec<ProofTerm>),
}
