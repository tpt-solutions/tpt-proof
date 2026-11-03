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
use tpt_proof_kernel::axioms::declare_standard;
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
    let mut scope = Scope::default();
    for (name, sort) in &vc.vars {
        scope.sorts.insert(name.clone(), *sort);
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

    fn is_bool_var(&self, name: &str) -> bool {
        self.sorts.get(name) == Some(&VcSort::Bool)
    }

    /// Whether an expression has integer sort.
    fn is_int(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Int(_) | Expr::Add(..) | Expr::Sub(..) | Expr::Mul(..) => true,
            Expr::Div(..) | Expr::Rem(..) => true,
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
            Expr::Var(name) if self.is_int_var(name) => Term::constant(name),
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
                Some((Sexp::List(_), _)) => Err(ReflectError::Unsupported(
                    "an indexed rule such as `th-lemma`".to_string(),
                )),
                _ => Err(ReflectError::Malformed("empty proof step".to_string())),
            },
            Sexp::Atom(other) => Err(ReflectError::Malformed(format!("unexpected `{other}`"))),
        }
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
                Some(Sexp::Atom(head)) if head == "+" || head == "-" || head == "*"
            ),
        }
    }

    /// Reads an integer term of the solver's text.
    fn term(&self, sexp: &Sexp) -> Result<Term, ReflectError> {
        match self.resolve(sexp) {
            Sexp::Atom(name) if is_numeral(name) || self.scope.is_int_var(name) => {
                Ok(Term::constant(name))
            }
            Sexp::List(items) => match items.split_first() {
                Some((Sexp::Atom(head), [a])) if head == "-" => {
                    Ok(Term::app("neg", vec![self.term(a)?]))
                }
                Some((Sexp::Atom(head), args)) if matches!(head.as_str(), "+" | "-" | "*") => {
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
            "rewrite" => self.rewrite(conclusion),
            "commutativity" => self.equation_by_axiom(conclusion),
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
        if self.proves_by_tautology(&conclusion) {
            return Ok((ProofTerm::Taut(conclusion.clone()), conclusion));
        }
        match &conclusion {
            Formula::Iff(left, right) => {
                let forward = Formula::Imp(left.clone(), right.clone());
                let backward = Formula::Imp(right.clone(), left.clone());
                let forward_proof = self
                    .axiom_instance(&forward.encode())
                    .ok_or_else(|| unsupported_rewrite(&conclusion))?;
                let backward_proof = self
                    .axiom_instance(&backward.encode())
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
                if f == g && from.len() == to.len() && steps.len() == from.len() =>
            {
                for ((_, premise), (a, b)) in steps.iter().zip(from.iter().zip(to)) {
                    if *premise != Formula::Atom(Prop::Eq(a.clone(), b.clone())) {
                        return Err(ReflectError::Malformed(format!(
                            "`{f}` arguments do not match"
                        )));
                    }
                }
                let proofs = steps.into_iter().map(|(proof, _)| proof).collect();
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
