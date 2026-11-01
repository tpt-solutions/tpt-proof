//! Propositions, terms, and the proof term language.
//!
//! The logic is first-order over a single universe of individuals, extended
//! with second-order quantification over propositional variables. Propositions
//! are atoms, implication, equality between terms, predicate symbols applied to
//! terms, and two kinds of universal quantifier: over propositional variables
//! and over individuals. A proof of `p` is a term of type `p` (Curry-Howard).
//!
//! Terms are individual variables or applications of uninterpreted function
//! symbols. A constant is a symbol of arity zero. There is one sort, so every
//! individual is of the same type. Inductive types and induction are not
//! implemented yet; see `docs/design-inductive-types.md`.

use std::fmt;

/// A first-order term.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    /// An individual variable bound by an enclosing `forall` over individuals.
    Var(String),
    /// An uninterpreted function symbol applied to arguments. A symbol with no
    /// arguments is a constant.
    Fun(String, Vec<Term>),
}

impl Term {
    /// Builds an application of `symbol` to `args`.
    pub fn app(symbol: &str, args: Vec<Term>) -> Term {
        Term::Fun(symbol.to_string(), args)
    }

    /// Builds a constant, an application to no arguments.
    pub fn constant(symbol: &str) -> Term {
        Term::app(symbol, Vec::new())
    }

    /// Builds an individual variable.
    pub fn var(name: &str) -> Term {
        Term::Var(name.to_string())
    }

    /// Every individual variable in this term.
    pub(crate) fn free_vars(&self, out: &mut Vec<String>) {
        match self {
            Term::Var(name) => {
                if !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Term::Fun(_, args) => args.iter().for_each(|arg| arg.free_vars(out)),
        }
    }

    /// Replaces the individual variable `name` by `replacement`.
    pub(crate) fn substitute(&self, name: &str, replacement: &Term) -> Term {
        match self {
            Term::Var(var) if var == name => replacement.clone(),
            Term::Var(_) => self.clone(),
            Term::Fun(symbol, args) => Term::Fun(
                symbol.clone(),
                args.iter()
                    .map(|arg| arg.substitute(name, replacement))
                    .collect(),
            ),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{name}"),
            Term::Fun(symbol, args) if args.is_empty() => write!(f, "{symbol}"),
            Term::Fun(symbol, args) => {
                let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "{symbol}({})", args.join(", "))
            }
        }
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
    /// Universal quantification over individuals: `forall x. A`.
    ForallInd(String, Box<Prop>),
    /// Equality of two terms.
    Eq(Term, Term),
    /// A predicate symbol applied to terms.
    Pred(String, Vec<Term>),
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

    /// Builds the quantified proposition `forall name. body` over propositions.
    pub fn forall(name: &str, body: Prop) -> Prop {
        Prop::Forall(name.to_string(), Box::new(body))
    }

    /// Builds the quantified proposition `forall name. body` over individuals.
    pub fn forall_ind(name: &str, body: Prop) -> Prop {
        Prop::ForallInd(name.to_string(), Box::new(body))
    }

    /// Whether the propositional variable `name` occurs free in this proposition.
    pub fn has_free(&self, name: &str) -> bool {
        match self {
            Prop::Atom(atom) => atom == name,
            Prop::Imp(a, b) => a.has_free(name) || b.has_free(name),
            Prop::Forall(bound, body) => bound != name && body.has_free(name),
            Prop::ForallInd(_, body) => body.has_free(name),
            Prop::Eq(_, _) | Prop::Pred(_, _) => false,
        }
    }

    /// Whether the individual variable `name` occurs free in this proposition.
    pub fn has_free_individual(&self, name: &str) -> bool {
        let mut out = Vec::new();
        self.free_individuals(&mut out);
        out.iter().any(|n| n == name)
    }

    /// Every free propositional variable name in this proposition.
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
            Prop::ForallInd(_, body) => body.free_vars(out),
            Prop::Eq(_, _) | Prop::Pred(_, _) => {}
        }
    }

    /// Every free individual variable name in this proposition.
    pub(crate) fn free_individuals(&self, out: &mut Vec<String>) {
        match self {
            Prop::Atom(_) => {}
            Prop::Imp(a, b) => {
                a.free_individuals(out);
                b.free_individuals(out);
            }
            Prop::Forall(_, body) => body.free_individuals(out),
            Prop::ForallInd(bound, body) => {
                let mut inner = Vec::new();
                body.free_individuals(&mut inner);
                for name in inner {
                    if name != *bound && !out.contains(&name) {
                        out.push(name);
                    }
                }
            }
            Prop::Eq(left, right) => {
                left.free_vars(out);
                right.free_vars(out);
            }
            Prop::Pred(_, args) => args.iter().for_each(|arg| arg.free_vars(out)),
        }
    }

    /// Whether two propositions are equal up to renaming of bound variables.
    pub fn alpha_eq(&self, other: &Prop) -> bool {
        alpha_eq(self, other)
    }

    /// Substitutes `replacement` for the free propositional variable `name`,
    /// renaming bound variables where needed so that no free variable is captured.
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
            Prop::ForallInd(bound, body) => {
                let mut replacement_individuals = Vec::new();
                replacement.free_individuals(&mut replacement_individuals);
                if replacement_individuals.contains(bound) {
                    let fresh = fresh_name(bound, &replacement_individuals, body);
                    let renamed = body.subst_individual(bound, &Term::Var(fresh.clone()));
                    Prop::forall_ind(&fresh, renamed.substitute(name, replacement))
                } else {
                    Prop::forall_ind(bound, body.substitute(name, replacement))
                }
            }
            Prop::Eq(_, _) | Prop::Pred(_, _) => self.clone(),
        }
    }

    /// Substitutes the term `replacement` for the free individual variable
    /// `name`, renaming bound individual variables where needed.
    pub(crate) fn subst_individual(&self, name: &str, replacement: &Term) -> Prop {
        match self {
            Prop::Atom(_) => self.clone(),
            Prop::Imp(a, b) => Prop::imp(
                a.subst_individual(name, replacement),
                b.subst_individual(name, replacement),
            ),
            Prop::Forall(bound, body) => {
                Prop::forall(bound, body.subst_individual(name, replacement))
            }
            Prop::ForallInd(bound, body) if bound == name => self.clone(),
            Prop::ForallInd(bound, body) => {
                let mut replacement_vars = Vec::new();
                replacement.free_vars(&mut replacement_vars);
                if replacement_vars.contains(bound) {
                    let fresh = fresh_name(bound, &replacement_vars, body);
                    let renamed = body.subst_individual(bound, &Term::Var(fresh.clone()));
                    Prop::forall_ind(&fresh, renamed.subst_individual(name, replacement))
                } else {
                    Prop::forall_ind(bound, body.subst_individual(name, replacement))
                }
            }
            Prop::Eq(left, right) => Prop::Eq(
                left.substitute(name, replacement),
                right.substitute(name, replacement),
            ),
            Prop::Pred(symbol, args) => Prop::Pred(
                symbol.clone(),
                args.iter()
                    .map(|arg| arg.substitute(name, replacement))
                    .collect(),
            ),
        }
    }
}

/// A name based on `base` that is not in `avoid` and not free in `body`.
fn fresh_name(base: &str, avoid: &[String], body: &Prop) -> String {
    let mut in_body = Vec::new();
    body.free_individuals(&mut in_body);
    let mut candidate = format!("{base}'");
    while avoid.contains(&candidate) || in_body.contains(&candidate) {
        candidate.push('\'');
    }
    candidate
}

/// Bound-variable correspondences for alpha-equivalence, innermost last.
#[derive(Default)]
struct Scope {
    props: Vec<(String, String)>,
    individuals: Vec<(String, String)>,
}

/// Equality up to renaming of bound variables.
pub(crate) fn alpha_eq(a: &Prop, b: &Prop) -> bool {
    alpha_eq_in(a, b, &mut Scope::default())
}

/// Two names match if they are bound at the same depth on both sides, or are
/// the same free name.
fn bound_match(scope: &[(String, String)], x: &str, y: &str) -> bool {
    let left = scope.iter().rposition(|(bound, _)| bound == x);
    let right = scope.iter().rposition(|(_, bound)| bound == y);
    match (left, right) {
        (Some(i), Some(j)) => i == j,
        (None, None) => x == y,
        _ => false,
    }
}

fn term_alpha_eq(a: &Term, b: &Term, scope: &Scope) -> bool {
    match (a, b) {
        (Term::Var(x), Term::Var(y)) => bound_match(&scope.individuals, x, y),
        (Term::Fun(f, xs), Term::Fun(g, ys)) => {
            f == g
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| term_alpha_eq(x, y, scope))
        }
        _ => false,
    }
}

fn alpha_eq_in(a: &Prop, b: &Prop, scope: &mut Scope) -> bool {
    match (a, b) {
        (Prop::Atom(x), Prop::Atom(y)) => bound_match(&scope.props, x, y),
        (Prop::Imp(a1, b1), Prop::Imp(a2, b2)) => {
            alpha_eq_in(a1, a2, scope) && alpha_eq_in(b1, b2, scope)
        }
        (Prop::Forall(x, body1), Prop::Forall(y, body2)) => {
            scope.props.push((x.clone(), y.clone()));
            let equal = alpha_eq_in(body1, body2, scope);
            scope.props.pop();
            equal
        }
        (Prop::ForallInd(x, body1), Prop::ForallInd(y, body2)) => {
            scope.individuals.push((x.clone(), y.clone()));
            let equal = alpha_eq_in(body1, body2, scope);
            scope.individuals.pop();
            equal
        }
        (Prop::Eq(l1, r1), Prop::Eq(l2, r2)) => {
            term_alpha_eq(l1, l2, scope) && term_alpha_eq(r1, r2, scope)
        }
        (Prop::Pred(p1, a1), Prop::Pred(p2, a2)) => {
            p1 == p2
                && a1.len() == a2.len()
                && a1.iter().zip(a2).all(|(x, y)| term_alpha_eq(x, y, scope))
        }
        _ => false,
    }
}

impl fmt::Display for Prop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prop::Atom(name) => write!(f, "{name}"),
            Prop::Imp(a, b) => write!(f, "({a} -> {b})"),
            Prop::Forall(name, body) => write!(f, "(forall {name}. {body})"),
            Prop::ForallInd(name, body) => write!(f, "(all {name}. {body})"),
            Prop::Eq(l, r) => write!(f, "({l} = {r})"),
            Prop::Pred(symbol, args) if args.is_empty() => write!(f, "{symbol}"),
            Prop::Pred(symbol, args) => {
                let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "{symbol}({})", args.join(", "))
            }
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
    /// Universal introduction over propositions: `Λ name. body`.
    TyLam(String, Box<ProofTerm>),
    /// Universal elimination over propositions: instantiates at a proposition.
    TyApp(Box<ProofTerm>, Prop),
    /// Universal introduction over individuals: proves `forall name. A`.
    IndLam(String, Box<ProofTerm>),
    /// Universal elimination over individuals: instantiates at a term.
    IndApp(Box<ProofTerm>, Term),
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
