//! Proof reconstruction: checking Z3's proof of an `unsat` VC in the kernel.
//!
//! Z3 and this module are both untrusted. The module reads the proof object
//! that Z3 prints for an `unsat` answer and turns each step into a kernel proof
//! term. The kernel then checks the whole term against the claim, so a wrong
//! translation is rejected, never accepted. A step that is not translated is
//! reported as [`ReflectError::Unsupported`]; it is never guessed.
//!
//! The claim is the VC itself: the assumptions imply the goal. Z3 refutes the
//! assumptions together with the negated goal, so the translation turns that
//! refutation into a proof of the goal, using the tautology rule for the
//! classical step.
//!
//! Each propositional Z3 step becomes a tautology lemma applied to its premises.
//! The integer steps use the standard axioms of [`tpt_proof_kernel::axioms`],
//! matched against the instance Z3 used, and the congruence rules
//! ([`ProofTerm::Leibniz`] and [`ProofTerm::Cong`]) for equalities of arguments.

// Kernel errors carry whole propositions, so the error type is large. See the
// kernel crate root, which allows the same lint for the same reason.
#![allow(clippy::result_large_err)]

use std::collections::BTreeMap;
use std::fmt;

use tpt_proof_kernel::arith::INT;
use tpt_proof_kernel::axioms::{declare_arrays, declare_division, declare_standard, ARRAY};
use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::terms::{ProofTerm, Prop, Sort, Term};
use tpt_proof_kernel::{Kernel, KernelError, Theorem};

use crate::smt::{parse_sexps, Sexp};
use crate::vc::{Expr, Sort as VcSort, Vc};

/// Why a proof could not be reconstructed. None of these says the VC is false.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectError {
    /// The solver output has no proof object, or the object is not well formed.
    Malformed(String),
    /// A rule, term, or formula form that the translator does not handle yet.
    Unsupported(String),
    /// The kernel rejected the translated proof.
    Rejected(KernelError),
}

impl fmt::Display for ReflectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReflectError::Malformed(reason) => write!(f, "malformed proof: {reason}"),
            ReflectError::Unsupported(what) => write!(f, "unsupported in proofs: {what}"),
            ReflectError::Rejected(err) => write!(f, "the kernel rejected the proof: {err}"),
        }
    }
}

impl std::error::Error for ReflectError {}

type Step = (ProofTerm, Formula);

/// The name of the lambda that binds hypothesis `index`.
fn hypothesis_name(index: usize) -> String {
    format!("#h{index}")
}

/// Checks Z3's proof of `vc` in the kernel. `proof` is the solver's output for
/// the script from [`crate::smt::encode_with_proof`]. On success the theorem
/// states that the assumptions of the VC imply its goal.
pub fn reconstruct(vc: &Vc, proof: &str) -> Result<Theorem, ReflectError> {
    let mut kernel = Kernel::new();
    declare_standard(&mut kernel).map_err(ReflectError::Rejected)?;
    declare_division(&mut kernel).map_err(ReflectError::Rejected)?;
    declare_arrays(&mut kernel).map_err(ReflectError::Rejected)?;
    let mut scope = Scope::default();
    for (name, sort) in &vc.vars {
        scope.sorts.insert(name.clone(), *sort);
        if *sort == VcSort::IntArray {
            kernel
                .declare_function_sorted(name, Vec::new(), Sort::named(ARRAY))
                .map_err(ReflectError::Rejected)?;
        }
        if *sort == VcSort::Int {
            kernel
                .declare_function_sorted(name, Vec::new(), Sort::named(INT))
                .map_err(ReflectError::Rejected)?;
        }
    }

    let assumptions: Vec<Formula> = vc
        .assumptions
        .iter()
        .map(|expr| scope.formula(expr))
        .collect::<Result<_, _>>()?;
    let goal = scope.formula(&vc.goal)?;
    // Z3 refutes the assumptions together with the negated goal, in this order.
    let mut hypotheses = assumptions.clone();
    hypotheses.push(Formula::Not(Box::new(goal.clone())));

    let sexps = parse_sexps(proof);
    let body = find_proof(&sexps).ok_or_else(|| {
        ReflectError::Malformed("no proof object in the solver output".to_string())
    })?;
    let mut translator = Translator {
        kernel: &kernel,
        scope: &scope,
        hypotheses: &hypotheses,
        env: BTreeMap::new(),
        terms: BTreeMap::new(),
    };
    let (body_proof, body_formula) = translator.step(body)?;
    if body_formula != Formula::Const(false) {
        return Err(ReflectError::Malformed(
            "the proof does not conclude false".to_string(),
        ));
    }

    // From the refutation `not goal -> false`, the double negation gives the goal.
    let last = hypotheses.len() - 1;
    let dne = Formula::Imp(
        Box::new(Formula::Not(Box::new(Formula::Not(Box::new(goal.clone()))))),
        Box::new(goal.clone()),
    );
    let refutation = ProofTerm::Lam(
        hypothesis_name(last),
        hypotheses[last].encode(),
        Box::new(body_proof),
    );
    let mut term = ProofTerm::App(Box::new(ProofTerm::Taut(dne)), Box::new(refutation));
    for index in (0..last).rev() {
        term = ProofTerm::Lam(
            hypothesis_name(index),
            hypotheses[index].encode(),
            Box::new(term),
        );
    }

    let claim = assumptions
        .iter()
        .rev()
        .fold(goal, |acc, assumption| {
            Formula::Imp(Box::new(assumption.clone()), Box::new(acc))
        })
        .encode();
    kernel
        .check_proof(&term, &claim)
        .map_err(ReflectError::Rejected)
}

/// Finds the body of the `(proof ...)` form in the solver output.
fn find_proof(sexps: &[Sexp]) -> Option<&Sexp> {
    for sexp in sexps {
        if let Sexp::List(items) = sexp {
            if matches!(items.first(), Some(Sexp::Atom(head)) if head == "proof") {
                return items.get(1);
            }
            if let Some(found) = find_proof(items) {
                return Some(found);
            }
        }
    }
    None
}

/// The sorts of the VC's variables, for reading terms and formulas.
#[derive(Default)]
struct Scope {
    sorts: BTreeMap<String, VcSort>,
}

impl Scope {
    fn is_int_var(&self, name: &str) -> bool {
        self.sorts.get(name) == Some(&VcSort::Int)
    }

    fn is_array_var(&self, name: &str) -> bool {
        self.sorts.get(name) == Some(&VcSort::IntArray)
    }

    fn is_bool_var(&self, name: &str) -> bool {
        self.sorts.get(name) == Some(&VcSort::Bool)
    }

    /// Whether an expression has integer sort.
    fn is_int(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Int(_) | Expr::Add(..) | Expr::Sub(..) | Expr::Mul(..) => true,
            Expr::Div(..) | Expr::Rem(..) | Expr::Select(..) => true,
            Expr::Var(name) => self.is_int_var(name),
            Expr::Ite(_, then, _) => self.is_int(then),
            _ => false,
        }
    }

    fn formula(&self, expr: &Expr) -> Result<Formula, ReflectError> {
        Ok(match expr {
            Expr::Bool(value) => Formula::Const(*value),
            Expr::Var(name) if self.is_bool_var(name) => Formula::Atom(Prop::atom(name)),
            Expr::Not(a) => Formula::Not(Box::new(self.formula(a)?)),
            Expr::And(items) => unit_connective(Formula::And(self.formulas(items)?)),
            Expr::Or(items) => unit_connective(Formula::Or(self.formulas(items)?)),
            Expr::Implies(a, b) => {
                Formula::Imp(Box::new(self.formula(a)?), Box::new(self.formula(b)?))
            }
            Expr::Eq(a, b) if self.is_int(a) => {
                Formula::Atom(Prop::Eq(self.term(a)?, self.term(b)?))
            }
            Expr::Eq(a, b) => Formula::Iff(Box::new(self.formula(a)?), Box::new(self.formula(b)?)),
            Expr::Lt(a, b) => Formula::Atom(Prop::Pred(
                "<".to_string(),
                vec![self.term(a)?, self.term(b)?],
            )),
            Expr::Le(a, b) => Formula::Atom(Prop::Pred(
                "<=".to_string(),
                vec![self.term(a)?, self.term(b)?],
            )),
            other => return Err(ReflectError::Unsupported(format!("formula `{other:?}`"))),
        })
    }

    fn formulas(&self, items: &[Expr]) -> Result<Vec<Formula>, ReflectError> {
        items.iter().map(|item| self.formula(item)).collect()
    }

    fn term(&self, expr: &Expr) -> Result<Term, ReflectError> {
        Ok(match expr {
            Expr::Int(value) if *value < 0 => Term::app(
                "neg",
                vec![Term::constant(&value.unsigned_abs().to_string())],
            ),
            Expr::Int(value) => Term::constant(&value.to_string()),
            Expr::Var(name) if self.is_int_var(name) || self.is_array_var(name) => {
                Term::constant(name)
            }
            Expr::Div(a, b) => Term::app("div", vec![self.term(a)?, self.term(b)?]),
            Expr::Rem(a, b) => Term::app("mod", vec![self.term(a)?, self.term(b)?]),
            Expr::Select(a, i) => Term::app("select", vec![self.term(a)?, self.term(i)?]),
            Expr::Store(a, i, v) => {
                Term::app("store", vec![self.term(a)?, self.term(i)?, self.term(v)?])
            }
            Expr::Add(a, b) => Term::app("+", vec![self.term(a)?, self.term(b)?]),
            Expr::Sub(a, b) => Term::app("-", vec![self.term(a)?, self.term(b)?]),
            Expr::Mul(a, b) => Term::app("*", vec![self.term(a)?, self.term(b)?]),
            other => return Err(ReflectError::Unsupported(format!("term `{other:?}`"))),
        })
    }
}

/// Translates Z3's proof steps into kernel proof terms.
struct Translator<'a> {
    kernel: &'a Kernel,
    scope: &'a Scope,
    hypotheses: &'a [Formula],
    /// The formula each `let`-bound proof or formula name stands for.
    env: BTreeMap<String, Formula>,
    /// The term each `let`-bound term name (`?x`) stands for.
    terms: BTreeMap<String, Sexp>,
}

impl Translator<'_> {
    /// Follows `?x` term names to the term they stand for.
    fn resolve<'b>(&'b self, sexp: &'b Sexp) -> &'b Sexp {
        match sexp {
            Sexp::Atom(name) if name.starts_with('?') => match self.terms.get(name) {
                Some(value) => self.resolve(value),
                None => sexp,
            },
            _ => sexp,
        }
    }

    /// Translates one proof step, or a reference to one, to a proof term and the
    /// formula it proves.
    fn step(&mut self, sexp: &Sexp) -> Result<Step, ReflectError> {
        match sexp {
            Sexp::Atom(name) if name.starts_with('@') => {
                let formula =
                    self.env.get(name).cloned().ok_or_else(|| {
                        ReflectError::Malformed(format!("unbound proof `{name}`"))
                    })?;
                Ok((ProofTerm::Var(name.clone()), formula))
            }
            Sexp::List(items) => match items.split_first() {
                Some((Sexp::Atom(head), rest)) if head == "let" => self.let_form(rest),
                Some((Sexp::Atom(rule), args)) => self.rule(rule, args),
                // An indexed rule, such as `((_ th-lemma arith farkas ...) ...)`.
                Some((Sexp::List(head), args)) => self.indexed_rule(head, args),
                _ => Err(ReflectError::Malformed("empty proof step".to_string())),
            },
            Sexp::Atom(other) => Err(ReflectError::Malformed(format!("unexpected `{other}`"))),
        }
    }

    /// An indexed rule. Only `(_ th-lemma arith farkas c1 ... cn)` is read: a
    /// clause of integer comparisons, with one coefficient per literal.
    fn indexed_rule(&self, head: &[Sexp], args: &[Sexp]) -> Result<Step, ReflectError> {
        let atom = atom_text;
        // A bare `(_ th-lemma arith)` states an arithmetic fact without a kind.
        if matches!(
            head,
            [first, second, third]
                if atom(first) == Some("_") && atom(second) == Some("th-lemma") && atom(third) == Some("arith")
        ) {
            return match args {
                [clause] => self.euclid_lemma(clause),
                _ => Err(ReflectError::Unsupported(
                    "a theory lemma with premise proofs in its arguments".to_string(),
                )),
            };
        }
        let is_th_lemma = matches!(
            head,
            [first, second, third, _, ..]
                if atom(first) == Some("_")
                    && atom(second) == Some("th-lemma")
                    && atom(third) == Some("arith")
        );
        let kind = head.get(3).and_then(atom);
        if !is_th_lemma || !matches!(kind, Some("farkas" | "assign-bounds")) {
            return Err(ReflectError::Unsupported(
                "an indexed rule such as `th-lemma`".to_string(),
            ));
        }
        let [clause] = args else {
            // Z3 can also put premise proofs in the argument list of a lemma. Those
            // are not decoded, so the step is reported as unsupported.
            return Err(ReflectError::Unsupported(
                "a theory lemma with premise proofs in its arguments".to_string(),
            ));
        };
        if kind == Some("assign-bounds") {
            // Z3's coefficients for bound propagation do not follow the Farkas
            // convention, so the clause is refuted by a search over 0/1 coefficients.
            return self.farkas_lemma(None, clause);
        }
        let coefficients = head[4..]
            .iter()
            .map(|sexp| {
                atom(sexp)
                    .and_then(|text| text.parse::<i128>().ok())
                    .ok_or_else(|| {
                        ReflectError::Malformed(
                            "a Farkas coefficient is not an integer".to_string(),
                        )
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.farkas_lemma(Some(&coefficients), clause)
    }

    /// Proves a clause `L_1 or ... or L_n` by a Farkas certificate. Each literal
    /// must be an integer comparison `t <= s`. The negated literals are the
    /// premises of [`ProofTerm::Farkas`], which the kernel checks, and the
    /// tautology `(not L_1 -> ... -> false) -> clause` turns the refutation into
    /// the clause.
    /// A bare `(_ th-lemma arith)` clause that states the Euclidean identity of a
    /// remainder: `t = k * (t div k) + (t mod k)` among `false` literals. It is
    /// the instance of `div_mod_euclid` at `t` and `k`, with `0 < k` by evaluation.
    fn euclid_lemma(&self, clause: &Sexp) -> Result<Step, ReflectError> {
        let conclusion = self.formula(clause)?;
        let literals = match &conclusion {
            Formula::Or(items) => items.clone(),
            other => vec![other.clone()],
        };
        for literal in &literals {
            let Formula::Atom(Prop::Eq(a, b)) = literal else {
                continue;
            };
            let Some((k, quotient, remainder)) = euclid_parts(b) else {
                continue;
            };
            if quotient != Term::app("div", vec![a.clone(), k.clone()])
                || remainder != Term::app("mod", vec![a.clone(), k.clone()])
            {
                continue;
            }
            let positive = Formula::Atom(Prop::Pred(
                "<".to_string(),
                vec![Term::constant("0"), k.clone()],
            ));
            let instance = ProofTerm::App(
                Box::new(ProofTerm::IndApp(
                    Box::new(ProofTerm::IndApp(
                        Box::new(ProofTerm::Axiom("div_mod_euclid".to_string())),
                        a.clone(),
                    )),
                    k,
                )),
                Box::new(ProofTerm::Taut(positive)),
            );
            let lemma = Formula::Imp(
                Box::new(Formula::Atom(Prop::Eq(a.clone(), b.clone()))),
                Box::new(conclusion.clone()),
            );
            return Ok((
                ProofTerm::App(Box::new(ProofTerm::Taut(lemma)), Box::new(instance)),
                conclusion,
            ));
        }
        Err(ReflectError::Unsupported(
            "a theory lemma of another shape".to_string(),
        ))
    }

    fn farkas_lemma(
        &self,
        coefficients: Option<&[i128]>,
        clause: &Sexp,
    ) -> Result<Step, ReflectError> {
        let conclusion = self.formula(clause)?;
        let literals = match &conclusion {
            Formula::Or(items) => items.clone(),
            other => vec![other.clone()],
        };
        if let Some(given) = coefficients {
            if literals.len() != given.len() {
                return Err(ReflectError::Malformed(format!(
                    "a Farkas lemma has {} literal(s) and {} coefficient(s)",
                    literals.len(),
                    given.len()
                )));
            }
        }
        let mut negations = Vec::new();
        for literal in &literals {
            match literal {
                Formula::Atom(Prop::Pred(symbol, _)) if symbol == "<=" => {
                    negations.push(Formula::Not(Box::new(literal.clone())));
                }
                // The negation of `not (t <= s)` is `t <= s`, a plain constraint.
                Formula::Not(inner) if matches!(&**inner, Formula::Atom(Prop::Pred(symbol, _)) if symbol == "<=") =>
                {
                    negations.push((**inner).clone());
                }
                other => {
                    return Err(ReflectError::Unsupported(format!(
                        "a Farkas literal `{}` is not an integer comparison",
                        describe(other)
                    )))
                }
            }
        }
        let refutation = negations
            .iter()
            .rev()
            .fold(Formula::Const(false), |acc, n| {
                Formula::Imp(Box::new(n.clone()), Box::new(acc))
            });
        // The encoding of `not (t <= s)` is `(t <= s) -> false`, the form the
        // kernel reads as a linear constraint.
        let premises: Vec<Prop> = negations.iter().map(Formula::encode).collect();
        let certificate = match coefficients {
            Some(given) => ProofTerm::Farkas(premises, given.to_vec()),
            None => self.searched_certificate(premises, &refutation)?,
        };
        let lemma = Formula::Imp(Box::new(refutation), Box::new(conclusion.clone()));
        Ok((
            ProofTerm::App(Box::new(ProofTerm::Taut(lemma)), Box::new(certificate)),
            conclusion,
        ))
    }

    /// The first certificate with coefficients 0 or 1 that the kernel accepts as a
    /// proof of `refutation`. The kernel checks each attempt, so the search cannot
    /// make a false lemma accepted.
    fn searched_certificate(
        &self,
        premises: Vec<Prop>,
        refutation: &Formula,
    ) -> Result<ProofTerm, ReflectError> {
        let count = premises.len();
        let claim = refutation.encode();
        for mask in 0..(1u64 << count.min(16)) {
            let coefficients: Vec<i128> =
                (0..count).map(|bit| ((mask >> bit) & 1) as i128).collect();
            let certificate = ProofTerm::Farkas(premises.clone(), coefficients);
            if self.kernel.check_proof(&certificate, &claim).is_ok() {
                return Ok(certificate);
            }
        }
        Err(ReflectError::Unsupported(
            "a theory lemma that linear arithmetic does not refute with 0/1 coefficients"
                .to_string(),
        ))
    }

    fn let_form(&mut self, rest: &[Sexp]) -> Result<Step, ReflectError> {
        match rest {
            [Sexp::List(bindings), body] => self.bindings(bindings, body),
            _ => Err(ReflectError::Malformed(
                "`let` needs bindings and a body".to_string(),
            )),
        }
    }

    /// Binds each `let` name in turn, then translates the body. A proof binding
    /// becomes a lambda, applied to the proof it names.
    fn bindings(&mut self, bindings: &[Sexp], body: &Sexp) -> Result<Step, ReflectError> {
        let Some((binding, rest)) = bindings.split_first() else {
            return self.step(body);
        };
        let (name, value) = match binding {
            Sexp::List(pair) => match pair.as_slice() {
                [Sexp::Atom(name), value] => (name, value),
                _ => {
                    return Err(ReflectError::Malformed(
                        "malformed `let` binding".to_string(),
                    ))
                }
            },
            Sexp::Atom(_) => {
                return Err(ReflectError::Malformed(
                    "malformed `let` binding".to_string(),
                ))
            }
        };
        if name.starts_with('$') {
            let formula = self.formula(value)?;
            self.env.insert(name.clone(), formula);
            return self.bindings(rest, body);
        }
        if name.starts_with('?') {
            self.terms.insert(name.clone(), value.clone());
            return self.bindings(rest, body);
        }
        if !name.starts_with('@') {
            return Err(ReflectError::Unsupported(format!("`let` name `{name}`")));
        }
        let (proof, formula) = self.step(value)?;
        self.env.insert(name.clone(), formula.clone());
        let (inner, inner_formula) = self.bindings(rest, body)?;
        let bound = ProofTerm::Lam(name.clone(), formula.encode(), Box::new(inner));
        Ok((
            ProofTerm::App(Box::new(bound), Box::new(proof)),
            inner_formula,
        ))
    }

    /// Reads a formula of the solver's text, with its `let` names resolved.
    fn formula(&self, sexp: &Sexp) -> Result<Formula, ReflectError> {
        match self.resolve(sexp) {
            Sexp::Atom(name) => {
                match name.as_str() {
                    "true" => Ok(Formula::Const(true)),
                    "false" => Ok(Formula::Const(false)),
                    _ if name.starts_with('$') => self.env.get(name).cloned().ok_or_else(|| {
                        ReflectError::Malformed(format!("unbound formula `{name}`"))
                    }),
                    _ if self.scope.is_bool_var(name) => Ok(Formula::Atom(Prop::atom(name))),
                    _ => Err(ReflectError::Unsupported(format!("formula `{name}`"))),
                }
            }
            Sexp::List(items) => {
                let Some((Sexp::Atom(head), args)) = items.split_first() else {
                    return Err(ReflectError::Malformed("empty formula".to_string()));
                };
                let formulas = |args: &[Sexp]| -> Result<Vec<Formula>, ReflectError> {
                    args.iter().map(|arg| self.formula(arg)).collect()
                };
                match (head.as_str(), args) {
                    ("not", [a]) => Ok(Formula::Not(Box::new(self.formula(a)?))),
                    ("and", _) => Ok(unit_connective(Formula::And(formulas(args)?))),
                    ("or", _) => Ok(unit_connective(Formula::Or(formulas(args)?))),
                    ("=>", [a, b]) => Ok(Formula::Imp(
                        Box::new(self.formula(a)?),
                        Box::new(self.formula(b)?),
                    )),
                    ("=", [a, b]) if self.is_int(a) || self.is_int(b) => {
                        Ok(Formula::Atom(Prop::Eq(self.term(a)?, self.term(b)?)))
                    }
                    ("=", [a, b]) => Ok(Formula::Iff(
                        Box::new(self.formula(a)?),
                        Box::new(self.formula(b)?),
                    )),
                    ("<=", [a, b]) => Ok(Formula::Atom(Prop::Pred(
                        "<=".to_string(),
                        vec![self.term(a)?, self.term(b)?],
                    ))),
                    ("<", [a, b]) => Ok(Formula::Atom(Prop::Pred(
                        "<".to_string(),
                        vec![self.term(a)?, self.term(b)?],
                    ))),
                    (">=", [a, b]) => Ok(Formula::Atom(Prop::Pred(
                        "<=".to_string(),
                        vec![self.term(b)?, self.term(a)?],
                    ))),
                    (">", [a, b]) => Ok(Formula::Atom(Prop::Pred(
                        "<".to_string(),
                        vec![self.term(b)?, self.term(a)?],
                    ))),
                    (other, _) => Err(ReflectError::Unsupported(format!("formula `{other}`"))),
                }
            }
        }
    }

    /// Whether a solver term denotes an integer.
    fn is_int(&self, sexp: &Sexp) -> bool {
        match self.resolve(sexp) {
            Sexp::Atom(name) => is_numeral(name) || self.scope.is_int_var(name),
            Sexp::List(items) => matches!(
                items.first(),
                Some(Sexp::Atom(head)) if matches!(head.as_str(), "+" | "-" | "*" | "div" | "mod" | "select")
            ),
        }
    }

    /// Reads an integer term of the solver's text.
    fn term(&self, sexp: &Sexp) -> Result<Term, ReflectError> {
        match self.resolve(sexp) {
            Sexp::Atom(name)
                if is_numeral(name)
                    || self.scope.is_int_var(name)
                    || self.scope.is_array_var(name) =>
            {
                Ok(Term::constant(name))
            }
            Sexp::List(items) => match items.split_first() {
                Some((Sexp::Atom(head), [a])) if head == "-" => {
                    Ok(Term::app("neg", vec![self.term(a)?]))
                }
                Some((Sexp::Atom(head), [array, index])) if head == "select" => Ok(Term::app(
                    "select",
                    vec![self.term(array)?, self.term(index)?],
                )),
                Some((Sexp::Atom(head), [array, index, value])) if head == "store" => {
                    Ok(Term::app(
                        "store",
                        vec![self.term(array)?, self.term(index)?, self.term(value)?],
                    ))
                }
                Some((Sexp::Atom(head), args))
                    if matches!(head.as_str(), "+" | "-" | "*" | "div" | "mod") =>
                {
                    let mut terms = args.iter().map(|arg| self.term(arg));
                    let first = terms.next().ok_or_else(|| {
                        ReflectError::Malformed(format!("`{head}` with no arguments"))
                    })??;
                    terms.try_fold(first, |acc, next| Ok(Term::app(head, vec![acc, next?])))
                }
                _ => Err(ReflectError::Unsupported(format!("term {sexp:?}"))),
            },
            Sexp::Atom(name) => Err(ReflectError::Unsupported(format!("term `{name}`"))),
        }
    }

    /// Dispatches on a rule. The last argument is the conclusion; the others
    /// are the premises.
    fn rule(&mut self, rule: &str, args: &[Sexp]) -> Result<Step, ReflectError> {
        let Some((conclusion, premises)) = args.split_last() else {
            return Err(ReflectError::Malformed(format!(
                "`{rule}` with no conclusion"
            )));
        };
        let conclusion = self.formula(conclusion)?;
        match rule {
            "asserted" => self.asserted(conclusion),
            "true-axiom" if conclusion == Formula::Const(true) => {
                Ok((ProofTerm::Taut(conclusion.clone()), conclusion))
            }
            "rewrite" => self.rewrite(conclusion),
            "commutativity" => match self.swapped_equivalence(conclusion.clone())? {
                Some(step) => Ok(step),
                None => self.equation_by_axiom(conclusion),
            },
            _ => {
                let mut steps = Vec::new();
                for premise in premises {
                    steps.push(self.step(premise)?);
                }
                match rule {
                    "mp" | "mp~" | "unit-resolution" | "and-elim" | "or-elim" | "not-or-elim"
                    | "iff-true" | "iff-false" => consequence(steps, conclusion),
                    "symm" => self.symm(steps, conclusion),
                    "trans" => self.trans(steps, conclusion),
                    "refl" => self.refl(conclusion),
                    "monotonicity" => self.monotonicity(steps, conclusion),
                    other => Err(ReflectError::Unsupported(format!("rule `{other}`"))),
                }
            }
        }
    }

    /// `(a = b) <-> (b = a)`, which holds by symmetry of equality. Each direction
    /// is the symmetry of the equation, under a binder. `Ok(None)` when the
    /// conclusion has another shape.
    fn swapped_equivalence(&self, conclusion: Formula) -> Result<Option<Step>, ReflectError> {
        let Formula::Iff(left, right) = &conclusion else {
            return Ok(None);
        };
        let (Formula::Atom(Prop::Eq(a, b)), Formula::Atom(Prop::Eq(c, d))) = (&**left, &**right)
        else {
            return Ok(None);
        };
        if a != d || b != c {
            return Ok(None);
        }
        let symmetric = |from: &Formula| {
            ProofTerm::Lam(
                HYPOTHESIS.to_string(),
                from.encode(),
                Box::new(ProofTerm::Sym(Box::new(ProofTerm::Var(
                    HYPOTHESIS.to_string(),
                )))),
            )
        };
        let forward = Formula::Imp(left.clone(), right.clone());
        let backward = Formula::Imp(right.clone(), left.clone());
        let forward_proof = symmetric(left);
        let backward_proof = symmetric(right);
        consequence(
            vec![(forward_proof, forward), (backward_proof, backward)],
            conclusion,
        )
        .map(Some)
    }

    fn asserted(&self, formula: Formula) -> Result<Step, ReflectError> {
        match self
            .hypotheses
            .iter()
            .position(|hypothesis| *hypothesis == formula)
        {
            Some(index) => Ok((ProofTerm::Var(hypothesis_name(index)), formula)),
            None => Err(ReflectError::Malformed(
                "an asserted formula is not one of the VC's assumptions".to_string(),
            )),
        }
    }

    /// A rewrite is accepted when it is a tautology, or when each direction (or
    /// the one equation) is an instance of a standard axiom.
    fn rewrite(&self, conclusion: Formula) -> Result<Step, ReflectError> {
        if matches!(&conclusion, Formula::Atom(Prop::Eq(t, s)) if t == s) {
            return self.refl(conclusion);
        }
        if let Some(step) = self.swapped_equivalence(conclusion.clone())? {
            return Ok(step);
        }
        if self.proves_by_tautology(&conclusion) {
            return Ok((ProofTerm::Taut(conclusion.clone()), conclusion));
        }
        match &conclusion {
            Formula::Iff(left, right) if is_reflexive_truth(left, right) => {
                let forward = Formula::Imp(left.clone(), right.clone());
                let backward = Formula::Imp(right.clone(), left.clone());
                let forward_proof = reflexive_direction(&forward);
                let backward_proof = reflexive_direction(&backward);
                consequence(
                    vec![(forward_proof, forward), (backward_proof, backward)],
                    conclusion,
                )
            }
            Formula::Iff(left, right) if is_linear_refutation(left, right) => {
                let forward = Formula::Imp(left.clone(), right.clone());
                let backward = Formula::Imp(right.clone(), left.clone());
                let forward_proof = self
                    .refutation_direction(left, right)
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                let backward_proof = self
                    .refutation_direction(right, left)
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                consequence(
                    vec![(forward_proof, forward), (backward_proof, backward)],
                    conclusion,
                )
            }
            Formula::Iff(left, right) if is_linear_truth(left, right) => {
                let forward = Formula::Imp(left.clone(), right.clone());
                let backward = Formula::Imp(right.clone(), left.clone());
                let forward_proof = self
                    .truth_direction(left, right)
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                let backward_proof = self
                    .truth_direction(right, left)
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                consequence(
                    vec![(forward_proof, forward), (backward_proof, backward)],
                    conclusion,
                )
            }
            Formula::Iff(left, right) => {
                let forward = Formula::Imp(left.clone(), right.clone());
                let backward = Formula::Imp(right.clone(), left.clone());
                let forward_proof = self
                    .linear_proof(&forward)
                    .or_else(|| self.axiom_instance(&forward.encode()))
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                let backward_proof = self
                    .linear_proof(&backward)
                    .or_else(|| self.axiom_instance(&backward.encode()))
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                consequence(
                    vec![(forward_proof, forward), (backward_proof, backward)],
                    conclusion,
                )
            }
            Formula::Atom(Prop::Eq(..)) => self.equation_by_axiom(conclusion),
            _ => Err(unsupported_rewrite(&conclusion)),
        }
    }

    /// Proves an integer equation by an axiom instance, in either direction.
    fn equation_by_axiom(&self, conclusion: Formula) -> Result<Step, ReflectError> {
        let Formula::Atom(Prop::Eq(left, right)) = &conclusion else {
            return Err(ReflectError::Unsupported(format!(
                "`{}` is not an equation",
                describe(&conclusion)
            )));
        };
        if let Some(proof) = self.axiom_instance(&Prop::Eq(left.clone(), right.clone())) {
            return Ok((proof, conclusion));
        }
        // Two integer terms with the same linear form are equal by the identity rule.
        let identity = ProofTerm::Identity(left.clone(), right.clone());
        if self
            .kernel
            .check_proof(&identity, &Prop::Eq(left.clone(), right.clone()))
            .is_ok()
        {
            return Ok((identity, conclusion));
        }
        match self.axiom_instance(&Prop::Eq(right.clone(), left.clone())) {
            Some(proof) => Ok((ProofTerm::Sym(Box::new(proof)), conclusion)),
            None => Err(unsupported_rewrite(&conclusion)),
        }
    }

    fn symm(&self, steps: Vec<Step>, conclusion: Formula) -> Result<Step, ReflectError> {
        if let Formula::Atom(Prop::Eq(t, s)) = &conclusion {
            if let [(proof, Formula::Atom(Prop::Eq(a, b)))] = steps.as_slice() {
                if a == s && b == t {
                    return Ok((ProofTerm::Sym(Box::new(proof.clone())), conclusion));
                }
            }
            return Err(ReflectError::Malformed(
                "`symm` does not match its premise".to_string(),
            ));
        }
        consequence(steps, conclusion)
    }

    fn trans(&self, steps: Vec<Step>, conclusion: Formula) -> Result<Step, ReflectError> {
        if let Formula::Atom(Prop::Eq(t, u)) = &conclusion {
            if let [(first, Formula::Atom(Prop::Eq(t1, s1))), (second, Formula::Atom(Prop::Eq(s2, u1)))] =
                steps.as_slice()
            {
                if t1 == t && u1 == u && s1 == s2 {
                    let proof = ProofTerm::Trans(Box::new(first.clone()), Box::new(second.clone()));
                    return Ok((proof, conclusion));
                }
            }
            return Err(ReflectError::Malformed(
                "`trans` does not chain its premises".to_string(),
            ));
        }
        consequence(steps, conclusion)
    }

    fn refl(&self, conclusion: Formula) -> Result<Step, ReflectError> {
        match &conclusion {
            Formula::Atom(Prop::Eq(t, s)) if t == s => Ok((ProofTerm::Refl(t.clone()), conclusion)),
            Formula::Iff(a, b) if a == b => Ok((ProofTerm::Taut(conclusion.clone()), conclusion)),
            _ => Err(ReflectError::Malformed(
                "`refl` of different sides".to_string(),
            )),
        }
    }

    /// Z3 lifts equivalences through a connective or an integer comparison.
    /// Connectives are checked as tautologies. Integer arguments are replaced
    /// one at a time with [`ProofTerm::Leibniz`]; an integer function is
    /// congruent with [`ProofTerm::Cong`].
    fn monotonicity(&self, steps: Vec<Step>, conclusion: Formula) -> Result<Step, ReflectError> {
        match &conclusion {
            Formula::Iff(from, to) => match (int_atom(from), int_atom(to)) {
                (Some((symbol, from_args)), Some((to_symbol, to_args)))
                    if symbol == to_symbol && from_args.len() == to_args.len() =>
                {
                    self.int_monotonicity(steps, &symbol, from_args, to_args, conclusion)
                }
                _ => consequence(steps, conclusion),
            },
            Formula::Atom(Prop::Eq(Term::Fun(f, from), Term::Fun(g, to)))
                if f == g && from.len() == to.len() =>
            {
                // Z3 gives a premise only for each changed argument. An unchanged
                // argument is reflexive, and each changed one is found among the
                // premises, in either direction.
                let mut proofs = Vec::new();
                for (a, b) in from.iter().zip(to) {
                    if a == b {
                        proofs.push(ProofTerm::Refl(a.clone()));
                        continue;
                    }
                    let proof = steps
                        .iter()
                        .find_map(|(proof, formula)| match formula {
                            Formula::Atom(Prop::Eq(l, r)) if l == a && r == b => {
                                Some(proof.clone())
                            }
                            Formula::Atom(Prop::Eq(l, r)) if l == b && r == a => {
                                Some(ProofTerm::Sym(Box::new(proof.clone())))
                            }
                            _ => None,
                        })
                        .ok_or_else(|| {
                            ReflectError::Malformed(format!(
                                "`{f}` arguments do not match: no premise equates them"
                            ))
                        })?;
                    proofs.push(proof);
                }
                Ok((ProofTerm::Cong(f.clone(), proofs), conclusion))
            }
            _ => Err(ReflectError::Unsupported(format!(
                "monotonicity over `{}`",
                describe(&conclusion)
            ))),
        }
    }

    /// Replaces the arguments of an integer atom one at a time. Each step is a
    /// [`ProofTerm::Leibniz`] in both directions, joined into an equivalence.
    fn int_monotonicity(
        &self,
        steps: Vec<Step>,
        symbol: &str,
        from: Vec<Term>,
        to: Vec<Term>,
        conclusion: Formula,
    ) -> Result<Step, ReflectError> {
        let original = Formula::Atom(rebuild(symbol, &from));
        let mut state = from.clone();
        let mut chain: Option<Step> = None;
        for index in 0..from.len() {
            if state[index] == to[index] {
                continue;
            }
            // Z3 gives one premise per changed argument, not one per argument,
            // and not in a fixed order. Find the one that equates this argument
            // with its target. Any other premise (such as a reflexive one) is
            // not used.
            let equation = steps
                .iter()
                .find_map(|(premise, formula)| match formula {
                    Formula::Atom(Prop::Eq(lhs, rhs))
                        if *lhs == state[index] && *rhs == to[index] =>
                    {
                        Some(premise.clone())
                    }
                    Formula::Atom(Prop::Eq(lhs, rhs))
                        if *rhs == state[index] && *lhs == to[index] =>
                    {
                        Some(ProofTerm::Sym(Box::new(premise.clone())))
                    }
                    _ => None,
                })
                .ok_or_else(|| {
                    ReflectError::Malformed("no premise equates a changed argument".to_string())
                })?;

            let before = Formula::Atom(rebuild(symbol, &state));
            let mut next = state.clone();
            next[index] = to[index].clone();
            let after = Formula::Atom(rebuild(symbol, &next));
            let mut motive_args = state.clone();
            motive_args[index] = Term::var(MOTIVE);
            let motive = rebuild(symbol, &motive_args);

            let forward = ProofTerm::Lam(
                HYPOTHESIS.to_string(),
                before.encode(),
                Box::new(ProofTerm::Leibniz(
                    MOTIVE.to_string(),
                    motive.clone(),
                    Box::new(equation.clone()),
                    Box::new(ProofTerm::Var(HYPOTHESIS.to_string())),
                )),
            );
            let backward = ProofTerm::Lam(
                HYPOTHESIS.to_string(),
                after.encode(),
                Box::new(ProofTerm::Leibniz(
                    MOTIVE.to_string(),
                    motive,
                    Box::new(ProofTerm::Sym(Box::new(equation))),
                    Box::new(ProofTerm::Var(HYPOTHESIS.to_string())),
                )),
            );
            let step = consequence(
                vec![
                    (
                        forward,
                        Formula::Imp(Box::new(before.clone()), Box::new(after.clone())),
                    ),
                    (
                        backward,
                        Formula::Imp(Box::new(after.clone()), Box::new(before.clone())),
                    ),
                ],
                Formula::Iff(Box::new(before), Box::new(after.clone())),
            )?;
            let joined_to = Formula::Iff(Box::new(original.clone()), Box::new(after));
            chain = Some(match chain {
                None => step,
                Some(previous) => consequence(vec![previous, step], joined_to)?,
            });
            state = next;
        }

        if state != to {
            return Err(ReflectError::Malformed(
                "the comparison's arguments do not all change".to_string(),
            ));
        }
        let step = match chain {
            Some(step) => step,
            None => consequence(
                Vec::new(),
                Formula::Iff(Box::new(original.clone()), Box::new(original)),
            )?,
        };
        if step.1 != conclusion {
            return Err(ReflectError::Malformed(
                "`monotonicity` does not give its conclusion".to_string(),
            ));
        }
        Ok(step)
    }

    /// Whether `formula` is a tautology, as the kernel checks it.
    fn proves_by_tautology(&self, formula: &Formula) -> bool {
        let proof = ProofTerm::Taut(formula.clone());
        self.kernel.check_proof(&proof, &formula.encode()).is_ok()
    }

    /// A proof of `from -> to` where one side is `true` and the other an integer
    /// comparison. `A -> true` is a tautology. `true -> A` holds when `A` is
    /// valid over the integers, which is `not not A -> A` once `not A` is refuted.
    fn truth_direction(&self, from: &Formula, to: &Formula) -> Option<ProofTerm> {
        match (from, to) {
            (_, Formula::Const(true)) => Some(ProofTerm::Taut(Formula::Imp(
                Box::new(from.clone()),
                Box::new(to.clone()),
            ))),
            (Formula::Const(true), atom) => {
                let negated = Formula::Not(Box::new(atom.clone())).encode();
                let refuted = contradiction_proof(self.kernel, &negated)?;
                let refuted_claim = Formula::Not(Box::new(Formula::Not(Box::new(atom.clone()))));
                let double_negation = ProofTerm::Taut(Formula::Imp(
                    Box::new(refuted_claim),
                    Box::new(atom.clone()),
                ));
                let proof = ProofTerm::Lam(
                    "#r".to_string(),
                    Formula::Const(true).encode(),
                    Box::new(ProofTerm::App(Box::new(double_negation), Box::new(refuted))),
                );
                let claim = Formula::Imp(Box::new(from.clone()), Box::new(to.clone())).encode();
                self.kernel.check_proof(&proof, &claim).ok().map(|_| proof)
            }
            _ => None,
        }
    }

    /// A proof of `from -> to` where one side is `false` and the other an integer
    /// comparison. `false -> A` is a tautology. `A -> false` holds when the
    /// comparison contradicts the facts that the division laws give about it.
    fn refutation_direction(&self, from: &Formula, to: &Formula) -> Option<ProofTerm> {
        match (from, to) {
            (Formula::Const(false), _) => Some(ProofTerm::Taut(Formula::Imp(
                Box::new(from.clone()),
                Box::new(to.clone()),
            ))),
            (atom, Formula::Const(false)) => {
                let proof = contradiction_proof(self.kernel, &atom.encode())?;
                let claim = Formula::Imp(Box::new(from.clone()), Box::new(to.clone())).encode();
                self.kernel.check_proof(&proof, &claim).ok().map(|_| proof)
            }
            _ => None,
        }
    }

    /// `t <= s -> t' <= s'` by the linear equivalence rule, when both sides are
    /// integer comparisons with the same linear form. The kernel must accept the
    /// proof, so a failed attempt falls back to the axioms.
    fn linear_proof(&self, formula: &Formula) -> Option<ProofTerm> {
        let Formula::Imp(from, to) = formula else {
            return None;
        };
        let (Formula::Atom(from), Formula::Atom(to)) = (&**from, &**to) else {
            return None;
        };
        let comparable = |prop: &Prop| matches!(prop, Prop::Pred(..) | Prop::Eq(..));
        if !comparable(from) || !comparable(to) {
            return None;
        }
        let proof = ProofTerm::Linear(from.clone(), to.clone());
        let claim = Prop::imp(from.clone(), to.clone());
        self.kernel.check_proof(&proof, &claim).ok().map(|_| proof)
    }

    /// An axiom instance that proves `target`, if a standard axiom has one.
    fn axiom_instance(&self, target: &Prop) -> Option<ProofTerm> {
        for axiom in self.kernel.axioms() {
            let mut binders = Vec::new();
            let mut body = &axiom.prop;
            while let Prop::ForallInd(name, _, inner) = body {
                binders.push(name.clone());
                body = inner;
            }
            let mut subst = Vec::new();
            if !match_prop(body, target, &mut subst) {
                continue;
            }
            let terms: Option<Vec<Term>> = binders
                .iter()
                .map(|binder| {
                    subst
                        .iter()
                        .find(|(name, _)| name == binder)
                        .map(|(_, term)| term.clone())
                })
                .collect();
            if let Some(terms) = terms {
                let proof = terms
                    .into_iter()
                    .fold(ProofTerm::Axiom(axiom.name.clone()), |proof, term| {
                        ProofTerm::IndApp(Box::new(proof), term)
                    });
                return Some(proof);
            }
        }
        None
    }
}

/// Whether the equivalence is `t = t` with `true`, in either order. Z3 writes
/// these for a reflexive equation that it has simplified.
fn is_reflexive_truth(left: &Formula, right: &Formula) -> bool {
    let reflexive = |formula: &Formula| matches!(formula, Formula::Atom(Prop::Eq(t, s)) if t == s);
    let truth = |formula: &Formula| matches!(formula, Formula::Const(true));
    (reflexive(left) && truth(right)) || (truth(left) && reflexive(right))
}

/// Proves one direction of a reflexive equivalence: `t = t -> true` is a
/// tautology, and `true -> t = t` is reflexivity under a binder.
fn reflexive_direction(formula: &Formula) -> ProofTerm {
    if let Formula::Imp(from, to) = formula {
        if let (Formula::Const(true), Formula::Atom(Prop::Eq(t, _))) = (&**from, &**to) {
            return ProofTerm::Lam(
                "#r".to_string(),
                Formula::Const(true).encode(),
                Box::new(ProofTerm::Refl(t.clone())),
            );
        }
    }
    ProofTerm::Taut(formula.clone())
}

/// The bound name of the argument that changes in a Leibniz motive.
const MOTIVE: &str = "#m";

/// The name of the hypothesis that a Leibniz step is applied to.
const HYPOTHESIS: &str = "#h";

/// Proves `conclusion` from the premises by a tautology over their formulas.
/// Each premise proof is applied to the tautology in turn.
fn consequence(steps: Vec<Step>, conclusion: Formula) -> Result<Step, ReflectError> {
    let lemma = steps
        .iter()
        .rev()
        .fold(conclusion.clone(), |acc, (_, premise)| {
            Formula::Imp(Box::new(premise.clone()), Box::new(acc))
        });
    let proof = steps
        .into_iter()
        .fold(ProofTerm::Taut(lemma), |proof, (premise, _)| {
            ProofTerm::App(Box::new(proof), Box::new(premise))
        });
    Ok((proof, conclusion))
}

/// Matches a standard axiom's body against a target. Pattern variables are the
/// individual variables of the axiom; `subst` collects their instances.
fn match_prop(pattern: &Prop, target: &Prop, subst: &mut Vec<(String, Term)>) -> bool {
    match (pattern, target) {
        (Prop::Atom(a), Prop::Atom(b)) => a == b,
        (Prop::Imp(a1, b1), Prop::Imp(a2, b2)) => {
            match_prop(a1, a2, subst) && match_prop(b1, b2, subst)
        }
        (Prop::Pred(s1, args1), Prop::Pred(s2, args2)) => {
            s1 == s2 && match_terms(args1, args2, subst)
        }
        (Prop::Eq(a1, b1), Prop::Eq(a2, b2)) => {
            match_terms(&[a1.clone(), b1.clone()], &[a2.clone(), b2.clone()], subst)
        }
        _ => false,
    }
}

fn match_terms(patterns: &[Term], targets: &[Term], subst: &mut Vec<(String, Term)>) -> bool {
    patterns.len() == targets.len()
        && patterns
            .iter()
            .zip(targets)
            .all(|(pattern, target)| match_term(pattern, target, subst))
}

fn match_term(pattern: &Term, target: &Term, subst: &mut Vec<(String, Term)>) -> bool {
    match (pattern, target) {
        (Term::Var(name), _) => match subst.iter().find(|(bound, _)| bound == name) {
            Some((_, bound)) => bound == target,
            None => {
                subst.push((name.clone(), target.clone()));
                true
            }
        },
        (Term::Fun(s1, args1), Term::Fun(s2, args2)) => {
            s1 == s2 && match_terms(args1, args2, subst)
        }
        _ => false,
    }
}

/// An integer atom as its symbol and arguments. Equations use the symbol `=`.
fn int_atom(formula: &Formula) -> Option<(String, Vec<Term>)> {
    match formula {
        Formula::Atom(Prop::Pred(symbol, args)) => Some((symbol.clone(), args.clone())),
        Formula::Atom(Prop::Eq(a, b)) => Some(("=".to_string(), vec![a.clone(), b.clone()])),
        _ => None,
    }
}

fn rebuild(symbol: &str, args: &[Term]) -> Prop {
    if symbol == "=" {
        Prop::Eq(args[0].clone(), args[1].clone())
    } else {
        Prop::Pred(symbol.to_string(), args.to_vec())
    }
}

fn is_numeral(name: &str) -> bool {
    !name.is_empty()
        && name.bytes().all(|b| b.is_ascii_digit())
        && (name == "0" || !name.starts_with('0'))
}

fn describe(formula: &Formula) -> String {
    format!("{formula:?}")
}

fn unsupported_rewrite(conclusion: &Formula) -> ReflectError {
    ReflectError::Unsupported(format!("rewrite of `{}`", describe(conclusion)))
}

/// A conjunction or disjunction of one formula is that formula. The solver
/// prints it that way, so the translation must too, or the two never match.
fn unit_connective(formula: Formula) -> Formula {
    match formula {
        Formula::And(mut items) | Formula::Or(mut items) if items.len() == 1 => items.remove(0),
        other => other,
    }
}

/// The text of a solver atom, or `None` for a list.
fn atom_text(sexp: &Sexp) -> Option<&str> {
    match sexp {
        Sexp::Atom(name) => Some(name.as_str()),
        Sexp::List(_) => None,
    }
}

/// Whether the equivalence is an integer comparison with `true`, in either order.
fn is_linear_truth(left: &Formula, right: &Formula) -> bool {
    let comparison = |formula: &Formula| matches!(formula, Formula::Atom(Prop::Pred(symbol, _)) if symbol == "<=" || symbol == "<");
    (comparison(left) && matches!(right, Formula::Const(true)))
        || (matches!(left, Formula::Const(true)) && comparison(right))
}

/// Whether the equivalence is an integer comparison with `false`, in either order.
fn is_linear_refutation(left: &Formula, right: &Formula) -> bool {
    let comparison = |formula: &Formula| matches!(formula, Formula::Atom(Prop::Pred(symbol, _)) if symbol == "<=" || symbol == "<");
    (comparison(left) && matches!(right, Formula::Const(false)))
        || (matches!(left, Formula::Const(false)) && comparison(right))
}

/// A proof of `case -> false`, where `case` is a comparison or its negation.
/// The Farkas rule refutes `case` together with facts about the remainders that
/// `case` mentions (see [`division_facts`]). Each fact is applied in turn, so the
/// result is `case -> false`. The kernel checks it; `None` if it does not refute.
fn contradiction_proof(kernel: &Kernel, case: &Prop) -> Option<ProofTerm> {
    let facts = division_facts(case);
    let mut premises: Vec<Prop> = facts.iter().map(|(fact, _)| fact.clone()).collect();
    premises.push(case.clone());
    let count = premises.len();
    // The certificate's coefficients are 0 or 1. The search tries each choice and
    // the kernel checks the one that works, so a wrong guess costs time, not truth.
    let claim = Prop::imp(case.clone(), Prop::atom("false"));
    for mask in 0..(1u64 << count.min(20)) {
        let coefficients: Vec<i128> = (0..count).map(|bit| ((mask >> bit) & 1) as i128).collect();
        let certificate = ProofTerm::Farkas(premises.clone(), coefficients);
        let proof = facts.iter().fold(certificate, |acc, (_, fact)| {
            ProofTerm::App(Box::new(acc), Box::new(fact.clone()))
        });
        if kernel.check_proof(&proof, &claim).is_ok() {
            return Some(proof);
        }
    }
    None
}

/// The facts the division laws give about each `t mod k` in `prop`, for a positive
/// numeral `k`: the remainder is not negative, and it is below `k`. Each fact is a
/// proof of a comparison, obtained by applying the axiom to `t` and `k` and to the
/// ground proof that `0 < k`.
fn division_facts(prop: &Prop) -> Vec<(Prop, ProofTerm)> {
    let mut remainders = Vec::new();
    collect_remainders_in_prop(prop, &mut remainders);

    let mut facts = Vec::new();
    for (term, divisor) in remainders {
        let k = Term::constant(&divisor);
        let positive = Formula::Atom(Prop::Pred(
            "<".to_string(),
            vec![Term::constant("0"), k.clone()],
        ));
        let modulo = Term::app("mod", vec![term.clone(), k.clone()]);
        let instance = |axiom: &str| {
            ProofTerm::App(
                Box::new(ProofTerm::IndApp(
                    Box::new(ProofTerm::IndApp(
                        Box::new(ProofTerm::Axiom(axiom.to_string())),
                        term.clone(),
                    )),
                    k.clone(),
                )),
                Box::new(ProofTerm::Taut(positive.clone())),
            )
        };
        facts.push((
            Prop::Pred("<=".to_string(), vec![Term::constant("0"), modulo.clone()]),
            instance("mod_nonneg"),
        ));
        facts.push((
            Prop::Pred("<".to_string(), vec![modulo, k.clone()]),
            instance("mod_lt_divisor"),
        ));
    }
    facts
}

/// The `(t, k)` of each `t mod k` in `prop` with a positive numeral `k`.
fn collect_remainders_in_prop(prop: &Prop, out: &mut Vec<(Term, String)>) {
    match prop {
        Prop::Pred(_, args) => args.iter().for_each(|t| collect_remainders(t, out)),
        Prop::Eq(a, b) => {
            collect_remainders(a, out);
            collect_remainders(b, out);
        }
        Prop::Imp(a, b) => {
            collect_remainders_in_prop(a, out);
            collect_remainders_in_prop(b, out);
        }
        _ => {}
    }
}

fn collect_remainders(term: &Term, out: &mut Vec<(Term, String)>) {
    if let Term::Fun(symbol, args) = term {
        if symbol == "mod" {
            if let [dividend, Term::Fun(divisor, no_args)] = args.as_slice() {
                let positive = no_args.is_empty()
                    && divisor != "0"
                    && divisor.bytes().all(|b| b.is_ascii_digit())
                    && !divisor.starts_with('0');
                if positive && !out.iter().any(|(t, k)| t == dividend && k == divisor) {
                    out.push((dividend.clone(), divisor.clone()));
                }
            }
        }
        args.iter().for_each(|arg| collect_remainders(arg, out));
    }
}

/// Reads `k * (t div k) + (t mod k)` into its divisor, quotient and remainder.
fn euclid_parts(term: &Term) -> Option<(Term, Term, Term)> {
    let Term::Fun(sum, parts) = term else {
        return None;
    };
    let [product, remainder] = parts.as_slice() else {
        return None;
    };
    let (Term::Fun(times, factors), "+") = (product, sum.as_str()) else {
        return None;
    };
    let [k, quotient] = factors.as_slice() else {
        return None;
    };
    if times != "*" {
        return None;
    }
    // The remainder is `mod(t, k)`, and the quotient `div(t, k)`, with the
    // same `t` and `k` checked by the caller.
    let Term::Fun(name, _) = remainder else {
        return None;
    };
    if name != "mod" {
        return None;
    }
    Some((k.clone(), quotient.clone(), remainder.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_reflexive_equation_iff_true_is_accepted_in_both_directions() {
        let mut kernel = Kernel::new();
        kernel
            .declare_function_sorted("x", Vec::new(), Sort::named(INT))
            .expect("declare x");
        let equation = Formula::Atom(Prop::Eq(Term::constant("x"), Term::constant("x")));
        let truth = Formula::Const(true);
        let forward = Formula::Imp(Box::new(equation.clone()), Box::new(truth.clone()));
        let backward = Formula::Imp(Box::new(truth), Box::new(equation));
        assert!(is_reflexive_truth(
            &Formula::Atom(Prop::Eq(Term::constant("x"), Term::constant("x"))),
            &Formula::Const(true)
        ));
        for formula in [&forward, &backward] {
            kernel
                .check_proof(&reflexive_direction(formula), &formula.encode())
                .expect("the direction is a theorem");
        }
    }

    #[test]
    fn an_unequal_pair_is_not_a_reflexive_truth() {
        let left = Formula::Atom(Prop::Eq(Term::constant("x"), Term::constant("y")));
        assert!(!is_reflexive_truth(&left, &Formula::Const(true)));
    }
}
