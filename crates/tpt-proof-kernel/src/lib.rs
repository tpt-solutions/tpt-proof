//! The trusted proof kernel for tpt-proof.
//!
//! This crate is the only trusted component of the framework (SPEC.md §4, §7).
//! It has no external dependencies and forbids `unsafe` code. The only way to
//! obtain a [`Theorem`] is through [`Kernel::check_proof`], so every theorem
//! value has been checked by this crate.

#![forbid(unsafe_code)]
// Kernel errors carry whole propositions, so the error type is large. Errors
// only occur on rejected proofs, never on the success path, so boxing them
// would complicate the API for no measurable gain.
#![allow(clippy::result_large_err)]

pub mod axioms;
mod checker;
pub mod terms;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub use axioms::Axiom;
pub use terms::{ProofTerm, Prop, Sort, Term};

/// Errors the kernel reports. A rejected proof is never accepted in part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    /// A `Var` refers to a name not bound in the local context.
    UnboundVariable(String),
    /// An individual variable is used outside the `forall` that binds it.
    UnboundIndividual(String),
    /// An `Axiom` refers to a name that was never declared.
    UnknownAxiom(String),
    /// A `Const` refers to a name that is not a checked theorem.
    UnknownTheorem(String),
    /// Application of a term whose type is not an implication.
    NotAFunction(Prop),
    /// A term has a different proposition than the one required.
    TypeMismatch {
        /// The proposition that was required.
        expected: Prop,
        /// The proposition the term actually proves.
        found: Prop,
    },
    /// Type application of a term whose type is not a universal quantifier.
    NotAForall(Prop),
    /// Individual application of a term whose type is not a universal quantifier over individuals.
    NotForallInd(Prop),
    /// Universal introduction over a variable the proof depends on.
    InvalidGeneralization {
        /// The variable that could not be generalized.
        variable: String,
        /// Why generalization is unsound here.
        reason: String,
    },
    /// A name is already used by an axiom, theorem, sort, or symbol.
    DuplicateName(String),
    /// A sort is used but was never declared.
    UnknownSort(String),
    /// A term or proposition uses a value of one sort where another is required.
    SortMismatch {
        /// The sort the position requires.
        expected: Sort,
        /// The sort of the value found there.
        found: Sort,
    },
    /// A function symbol in a term or proof is not declared.
    UnknownFunction(String),
    /// A predicate symbol in a proposition is not declared.
    UnknownPredicate(String),
    /// A function or predicate symbol is used with the wrong number of arguments.
    ArityMismatch {
        /// The function or predicate symbol.
        symbol: String,
        /// The arity it was declared with.
        expected: usize,
        /// The number of arguments given.
        found: usize,
    },
    /// Equality reasoning was applied to something that is not an equality.
    NotAnEquality(Prop),
    /// Transitivity was applied to equalities that do not share a middle term.
    TransitivityMismatch {
        /// The right-hand side of the first equality.
        middle: Term,
        /// The left-hand side of the second equality.
        found: Term,
    },
    /// An induction axiom was requested for a sort that was not declared inductively.
    NotInductive(String),
    /// An inductive type must have at least one constructor.
    NoConstructors(String),
    /// A recursive definition gives a case for something that is not a constructor of its sort.
    UnknownConstructor(String),
    /// A recursive definition has no case for a constructor.
    MissingCase(String),
    /// A recursive definition calls itself on something other than a recursive argument.
    NotStructural(String),
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::UnboundVariable(name) => write!(f, "unbound variable `{name}`"),
            KernelError::UnboundIndividual(name) => {
                write!(f, "individual `{name}` is not bound by a forall")
            }
            KernelError::UnknownAxiom(name) => write!(f, "unknown axiom `{name}`"),
            KernelError::UnknownTheorem(name) => write!(f, "unknown theorem `{name}`"),
            KernelError::NotAFunction(prop) => write!(f, "applied a non-function of type {prop}"),
            KernelError::TypeMismatch { expected, found } => {
                write!(f, "expected a proof of {expected}, found {found}")
            }
            KernelError::NotAForall(prop) => {
                write!(f, "instantiated a non-quantified term of type {prop}")
            }
            KernelError::NotForallInd(prop) => {
                write!(f, "instantiated a term of type {prop} at an individual")
            }
            KernelError::InvalidGeneralization { variable, reason } => {
                write!(f, "cannot generalize over `{variable}`: {reason}")
            }
            KernelError::DuplicateName(name) => write!(f, "name `{name}` is already declared"),
            KernelError::UnknownSort(name) => write!(f, "unknown sort `{name}`"),
            KernelError::SortMismatch { expected, found } => {
                write!(f, "expected a value of sort {expected}, found {found}")
            }
            KernelError::UnknownFunction(name) => write!(f, "unknown function symbol `{name}`"),
            KernelError::UnknownPredicate(name) => write!(f, "unknown predicate symbol `{name}`"),
            KernelError::ArityMismatch {
                symbol,
                expected,
                found,
            } => write!(f, "`{symbol}` takes {expected} argument(s), given {found}"),
            KernelError::NotAnEquality(prop) => write!(f, "expected an equality, found {prop}"),
            KernelError::TransitivityMismatch { middle, found } => {
                write!(
                    f,
                    "transitivity needs {middle} on both sides, found {found}"
                )
            }
            KernelError::NotInductive(name) => write!(f, "sort `{name}` is not an inductive type"),
            KernelError::NoConstructors(name) => {
                write!(f, "inductive type `{name}` needs at least one constructor")
            }
            KernelError::UnknownConstructor(name) => {
                write!(f, "`{name}` is not a constructor of this type")
            }
            KernelError::MissingCase(name) => write!(f, "no case for constructor `{name}`"),
            KernelError::NotStructural(symbol) => write!(
                f,
                "`{symbol}` may only be called on a recursive argument of its case"
            ),
        }
    }
}

impl std::error::Error for KernelError {}

/// Result type used throughout the kernel.
pub type Result<T> = std::result::Result<T, KernelError>;

/// A proposition proved by the kernel, together with the axioms it depends on.
///
/// The fields are private and the constructor is crate-private, so a `Theorem`
/// can only come from a successful check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Theorem {
    prop: Prop,
    axioms: BTreeSet<String>,
}

impl Theorem {
    pub(crate) fn new(prop: Prop, axioms: BTreeSet<String>) -> Self {
        Theorem { prop, axioms }
    }

    /// The proposition this theorem establishes.
    pub fn prop(&self) -> &Prop {
        &self.prop
    }

    /// Names of every axiom (including assumptions) this theorem depends on.
    pub fn axioms(&self) -> &BTreeSet<String> {
        &self.axioms
    }
}

/// The argument and result sorts of a function symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Signature {
    args: Vec<Sort>,
    result: Sort,
}

/// The kernel environment: declared sorts, symbols, axioms, and theorems.
#[derive(Debug, Default)]
pub struct Kernel {
    sorts: BTreeSet<String>,
    functions: BTreeMap<String, Signature>,
    predicates: BTreeMap<String, Vec<Sort>>,
    inductives: BTreeMap<String, Vec<(String, Vec<Sort>)>>,
    axioms: BTreeMap<String, Axiom>,
    theorems: BTreeMap<String, Theorem>,
    assumptions: usize,
}

impl Kernel {
    /// Creates a kernel with the default sort `Ind` and no axioms or theorems.
    pub fn new() -> Self {
        let mut kernel = Kernel::default();
        kernel.sorts.insert(Sort::ind().0);
        kernel
    }

    /// Declares a sort. Individuals of a sort are the values of that type.
    pub fn declare_sort(&mut self, name: &str) -> Result<Sort> {
        if self.sorts.contains(name) {
            return Err(KernelError::DuplicateName(name.to_string()));
        }
        self.sorts.insert(name.to_string());
        Ok(Sort::named(name))
    }

    /// Declares a trusted axiom. This expands the TCB, so every axiom must
    /// carry a justification, which is recorded with it. An axiom must be
    /// closed: it cannot mention an individual variable that nothing binds.
    pub fn declare_axiom(&mut self, name: &str, prop: Prop, justification: &str) -> Result<()> {
        self.ensure_fresh(name)?;
        self.check_prop(&prop, &[])?;
        let axiom = Axiom {
            name: name.to_string(),
            prop,
            justification: justification.to_string(),
        };
        self.axioms.insert(name.to_string(), axiom);
        Ok(())
    }

    /// Introduces an assumption for an interactive proof. It is tracked like an
    /// axiom: every theorem that uses it lists it in [`Theorem::axioms`].
    pub fn assume(&mut self, prop: Prop) -> Result<Theorem> {
        self.check_prop(&prop, &[])?;
        self.assumptions += 1;
        let name = format!("assumption#{}", self.assumptions);
        let axiom = Axiom {
            name: name.clone(),
            prop: prop.clone(),
            justification: "assumed explicitly in an interactive proof".to_string(),
        };
        self.axioms.insert(name.clone(), axiom);
        Ok(Theorem::new(prop, BTreeSet::from([name])))
    }

    /// Checks `term` against `claimed`. Returns a [`Theorem`] only if the proof
    /// is valid. The claim must be closed and use only declared symbols.
    pub fn check_proof(&self, term: &ProofTerm, claimed: &Prop) -> Result<Theorem> {
        self.check_prop(claimed, &[])?;
        let mut ctx = checker::Context::default();
        let mut deps = BTreeSet::new();
        let found = checker::infer(self, &mut ctx, term, &mut deps)?;
        if !crate::terms::alpha_eq(&found, claimed) {
            return Err(KernelError::TypeMismatch {
                expected: claimed.clone(),
                found,
            });
        }
        Ok(Theorem::new(claimed.clone(), deps))
    }

    /// Checks `term` against `claimed` and stores the result under `name`, so
    /// later proofs can refer to it with [`ProofTerm::Const`].
    pub fn declare_theorem(&mut self, name: &str, term: &ProofTerm, claimed: &Prop) -> Result<()> {
        self.ensure_fresh(name)?;
        let theorem = self.check_proof(term, claimed)?;
        self.theorems.insert(name.to_string(), theorem);
        Ok(())
    }

    /// Declares an uninterpreted function symbol over the default sort, with the
    /// given arity. A symbol with arity zero is a constant.
    pub fn declare_function(&mut self, symbol: &str, arity: usize) -> Result<()> {
        self.declare_function_sorted(symbol, vec![Sort::ind(); arity], Sort::ind())
    }

    /// Declares an uninterpreted function symbol with explicit argument and
    /// result sorts.
    pub fn declare_function_sorted(
        &mut self,
        symbol: &str,
        args: Vec<Sort>,
        result: Sort,
    ) -> Result<()> {
        self.check_sorts(args.iter().chain(std::iter::once(&result)))?;
        if self.functions.contains_key(symbol) {
            return Err(KernelError::DuplicateName(symbol.to_string()));
        }
        self.functions
            .insert(symbol.to_string(), Signature { args, result });
        Ok(())
    }

    /// Declares an uninterpreted predicate symbol over the default sort.
    pub fn declare_predicate(&mut self, symbol: &str, arity: usize) -> Result<()> {
        self.declare_predicate_sorted(symbol, vec![Sort::ind(); arity])
    }

    /// Declares an uninterpreted predicate symbol with explicit argument sorts.
    pub fn declare_predicate_sorted(&mut self, symbol: &str, args: Vec<Sort>) -> Result<()> {
        self.check_sorts(args.iter())?;
        if self.predicates.contains_key(symbol) {
            return Err(KernelError::DuplicateName(symbol.to_string()));
        }
        self.predicates.insert(symbol.to_string(), args);
        Ok(())
    }

    /// Declares an inductive type. It becomes a new sort, and each constructor
    /// is a function from its argument sorts to the new sort. An argument of the
    /// type being declared is a recursive argument.
    ///
    /// Positivity is automatic: constructor arguments are first-order values of
    /// declared sorts, so there are no function-typed arguments that could be
    /// non-positive.
    ///
    /// The constructors are trusted to generate the sort freely. That is the
    /// assumption behind [`Kernel::declare_induction`].
    pub fn declare_inductive(
        &mut self,
        name: &str,
        constructors: &[(&str, Vec<Sort>)],
    ) -> Result<Sort> {
        if self.sorts.contains(name) {
            return Err(KernelError::DuplicateName(name.to_string()));
        }
        if constructors.is_empty() {
            return Err(KernelError::NoConstructors(name.to_string()));
        }
        let sort = Sort::named(name);
        let mut seen = BTreeSet::new();
        for (constructor, args) in constructors {
            if !seen.insert(*constructor) || self.functions.contains_key(*constructor) {
                return Err(KernelError::DuplicateName(constructor.to_string()));
            }
            for arg in args {
                if arg != &sort && !self.sorts.contains(&arg.0) {
                    return Err(KernelError::UnknownSort(arg.0.clone()));
                }
            }
        }
        self.sorts.insert(name.to_string());
        let mut recorded = Vec::new();
        for (constructor, args) in constructors {
            self.functions.insert(
                constructor.to_string(),
                Signature {
                    args: args.clone(),
                    result: sort.clone(),
                },
            );
            recorded.push((constructor.to_string(), args.clone()));
        }
        self.inductives.insert(name.to_string(), recorded);
        Ok(sort)
    }

    /// Adds the induction axiom for an inductive sort and a predicate over it:
    ///
    /// ```text
    /// for each constructor C(a1..an):
    ///     forall a1..an. (P(ai) for each recursive ai) -> P(C(a1..an))
    ///   implies  forall x:T. P(x)
    /// ```
    ///
    /// The axiom is generated by the kernel from the declared constructors, so it
    /// is trusted exactly to the extent that the sort is generated freely by them.
    /// It is recorded as an axiom, so every theorem that uses it lists it.
    pub fn declare_induction(&mut self, axiom: &str, sort: &Sort, predicate: &str) -> Result<()> {
        let constructors = self
            .inductives
            .get(&sort.0)
            .cloned()
            .ok_or_else(|| KernelError::NotInductive(sort.0.clone()))?;
        let predicate_sorts = self
            .predicates
            .get(predicate)
            .cloned()
            .ok_or_else(|| KernelError::UnknownPredicate(predicate.to_string()))?;
        if predicate_sorts.len() != 1 {
            return Err(KernelError::ArityMismatch {
                symbol: predicate.to_string(),
                expected: 1,
                found: predicate_sorts.len(),
            });
        }
        if &predicate_sorts[0] != sort {
            return Err(KernelError::SortMismatch {
                expected: sort.clone(),
                found: predicate_sorts[0].clone(),
            });
        }

        let mut cases = Vec::new();
        for (constructor, args) in &constructors {
            let binders: Vec<String> = (0..args.len()).map(|j| format!("a{j}")).collect();
            let term = Term::app(constructor, binders.iter().map(|b| Term::var(b)).collect());
            let mut body = Prop::Pred(predicate.to_string(), vec![term]);
            for (binder, arg) in binders.iter().zip(args).rev() {
                if arg == sort {
                    let hypothesis = Prop::Pred(predicate.to_string(), vec![Term::var(binder)]);
                    body = Prop::imp(hypothesis, body);
                }
            }
            for (binder, arg) in binders.iter().zip(args).rev() {
                body = Prop::forall_sorted(binder, arg.clone(), body);
            }
            cases.push(body);
        }

        let mut prop = Prop::forall_sorted(
            "x",
            sort.clone(),
            Prop::Pred(predicate.to_string(), vec![Term::var("x")]),
        );
        for case in cases.into_iter().rev() {
            prop = Prop::imp(case, prop);
        }
        self.declare_axiom(
            axiom,
            prop,
            "induction principle: the sort is generated freely by its constructors",
        )
    }

    /// Defines `symbol : sort -> result` by structural recursion on an inductive
    /// sort. `cases` gives one body per constructor. Inside a body, the
    /// individual variables `a0`, `a1`, ... are the constructor's arguments, and
    /// the recursive results are written `symbol(a_j)` for each recursive
    /// argument `a_j`. Nothing else may call `symbol`.
    ///
    /// The kernel generates one defining equation per constructor, as a trusted
    /// axiom named `symbol_constructor`:
    ///
    /// ```text
    /// forall a0..an. symbol(C(a0..an)) = body
    /// ```
    ///
    /// Each equation fixes `symbol` on one constructor, and the recursive calls
    /// are on strictly smaller arguments, so the definition is conservative: it
    /// adds no new contradiction and terminates by construction.
    pub fn define_by_recursion(
        &mut self,
        symbol: &str,
        sort: &Sort,
        result: &Sort,
        cases: &[(&str, Term)],
    ) -> Result<()> {
        self.define_by_recursion_with_params(symbol, sort, &[], result, cases)
    }

    /// Like [`Kernel::define_by_recursion`], with extra parameters after the
    /// recursive argument. Inside a case, the parameters are the individual
    /// variables `p0`, `p1`, ... and the symbol takes them after its recursive
    /// argument: `symbol(a_j, t1, .., tk)`.
    ///
    /// Only the first argument must be structural. The other arguments may be any
    /// well-sorted terms, so a definition like `add(succ(a0), y) = succ(add(a0, y))`
    /// is accepted. It stays conservative for the same reason as before: each
    /// equation fixes the value on one constructor, and recursion goes down the
    /// first argument.
    pub fn define_by_recursion_with_params(
        &mut self,
        symbol: &str,
        sort: &Sort,
        params: &[Sort],
        result: &Sort,
        cases: &[(&str, Term)],
    ) -> Result<()> {
        let constructors = self
            .inductives
            .get(&sort.0)
            .cloned()
            .ok_or_else(|| KernelError::NotInductive(sort.0.clone()))?;
        self.check_sort(result)?;
        self.check_sorts(params.iter())?;
        if self.functions.contains_key(symbol) {
            return Err(KernelError::DuplicateName(symbol.to_string()));
        }

        let mut bodies: BTreeMap<&str, &Term> = BTreeMap::new();
        for (constructor, body) in cases {
            if !constructors.iter().any(|(name, _)| name == constructor) {
                return Err(KernelError::UnknownConstructor(constructor.to_string()));
            }
            if bodies.insert(constructor, body).is_some() {
                return Err(KernelError::DuplicateName(constructor.to_string()));
            }
        }
        for (constructor, _) in &constructors {
            if !bodies.contains_key(constructor.as_str()) {
                return Err(KernelError::MissingCase(constructor.clone()));
            }
        }

        // The symbol must be visible while its bodies are checked. Remove it
        // again if any check fails, so a rejected definition leaves no trace.
        let mut arg_sorts = vec![sort.clone()];
        arg_sorts.extend(params.iter().cloned());
        self.functions.insert(
            symbol.to_string(),
            Signature {
                args: arg_sorts,
                result: result.clone(),
            },
        );
        let equations =
            self.recursion_equations(symbol, sort, params, result, &constructors, &bodies);
        let equations = match equations {
            Ok(equations) => equations,
            Err(err) => {
                self.functions.remove(symbol);
                return Err(err);
            }
        };
        for (name, _) in &equations {
            if self.ensure_fresh(name).is_err() {
                self.functions.remove(symbol);
                return Err(KernelError::DuplicateName(name.clone()));
            }
        }
        for (name, prop) in equations {
            self.declare_axiom(
                &name,
                prop,
                "defining equation of a structurally recursive definition (conservative)",
            )?;
        }
        Ok(())
    }

    /// Checks every case body and returns the defining equation for each constructor.
    fn recursion_equations(
        &self,
        symbol: &str,
        sort: &Sort,
        params: &[Sort],
        result: &Sort,
        constructors: &[(String, Vec<Sort>)],
        bodies: &BTreeMap<&str, &Term>,
    ) -> Result<Vec<(String, Prop)>> {
        let param_names: Vec<String> = (0..params.len()).map(|i| format!("p{i}")).collect();
        let mut equations = Vec::new();
        for (constructor, args) in constructors {
            let body = bodies[constructor.as_str()];
            let binders: Vec<String> = (0..args.len()).map(|j| format!("a{j}")).collect();
            let mut scope: Vec<(String, Sort)> =
                binders.iter().cloned().zip(args.iter().cloned()).collect();
            scope.extend(param_names.iter().cloned().zip(params.iter().cloned()));
            let found = self.check_term_in(body, &scope)?;
            if &found != result {
                return Err(KernelError::SortMismatch {
                    expected: result.clone(),
                    found,
                });
            }
            let recursive: Vec<String> = binders
                .iter()
                .zip(args)
                .filter(|(_, arg)| *arg == sort)
                .map(|(binder, _)| binder.clone())
                .collect();
            check_structural(symbol, body, &recursive)?;

            let applied = Term::app(constructor, binders.iter().map(|b| Term::var(b)).collect());
            let mut call_args = vec![applied];
            call_args.extend(param_names.iter().map(|p| Term::var(p)));
            let mut prop = Prop::Eq(Term::app(symbol, call_args), (*body).clone());
            for (binder, arg) in binders.iter().zip(args).rev() {
                prop = Prop::forall_sorted(binder, arg.clone(), prop);
            }
            for (name, sort) in param_names.iter().zip(params).rev() {
                prop = Prop::forall_sorted(name, sort.clone(), prop);
            }
            equations.push((format!("{symbol}_{constructor}"), prop));
        }
        Ok(equations)
    }

    /// The argument and result sorts of a function symbol.
    pub(crate) fn signature(&self, symbol: &str) -> Option<(Vec<Sort>, Sort)> {
        self.functions
            .get(symbol)
            .map(|sig| (sig.args.clone(), sig.result.clone()))
    }

    /// The declared arity of a function symbol.
    pub fn arity(&self, symbol: &str) -> Option<usize> {
        self.functions.get(symbol).map(|sig| sig.args.len())
    }

    /// Checks that a closed term is well-formed and returns its sort.
    pub fn check_term(&self, term: &Term) -> Result<Sort> {
        self.check_term_in(term, &[])
    }

    /// Checks that a sort has been declared.
    pub(crate) fn check_sort(&self, sort: &Sort) -> Result<()> {
        self.check_sorts(std::iter::once(sort))
    }

    fn check_sorts<'a>(&self, sorts: impl Iterator<Item = &'a Sort>) -> Result<()> {
        for sort in sorts {
            if !self.sorts.contains(&sort.0) {
                return Err(KernelError::UnknownSort(sort.0.clone()));
            }
        }
        Ok(())
    }

    /// Checks a term whose individual variables are in `scope`, and returns its
    /// sort.
    pub(crate) fn check_term_in(&self, term: &Term, scope: &[(String, Sort)]) -> Result<Sort> {
        match term {
            Term::Var(name) => scope
                .iter()
                .rev()
                .find(|(bound, _)| bound == name)
                .map(|(_, sort)| sort.clone())
                .ok_or_else(|| KernelError::UnboundIndividual(name.clone())),
            Term::Fun(symbol, args) => {
                let signature = self
                    .functions
                    .get(symbol)
                    .ok_or_else(|| KernelError::UnknownFunction(symbol.clone()))?;
                if signature.args.len() != args.len() {
                    return Err(KernelError::ArityMismatch {
                        symbol: symbol.clone(),
                        expected: signature.args.len(),
                        found: args.len(),
                    });
                }
                for (arg, expected) in args.iter().zip(&signature.args) {
                    let found = self.check_term_in(arg, scope)?;
                    if &found != expected {
                        return Err(KernelError::SortMismatch {
                            expected: expected.clone(),
                            found,
                        });
                    }
                }
                Ok(signature.result.clone())
            }
        }
    }

    /// Checks that a proposition is well-formed: symbols are declared with the
    /// right sorts and arities, and individual variables are in `scope`.
    pub(crate) fn check_prop(&self, prop: &Prop, scope: &[(String, Sort)]) -> Result<()> {
        match prop {
            Prop::Atom(_) => Ok(()),
            Prop::Imp(a, b) => {
                self.check_prop(a, scope)?;
                self.check_prop(b, scope)
            }
            Prop::Forall(_, body) => self.check_prop(body, scope),
            Prop::ForallInd(name, sort, body) => {
                self.check_sort(sort)?;
                let mut inner = scope.to_vec();
                inner.push((name.clone(), sort.clone()));
                self.check_prop(body, &inner)
            }
            Prop::Eq(left, right) => {
                let left_sort = self.check_term_in(left, scope)?;
                let right_sort = self.check_term_in(right, scope)?;
                if left_sort != right_sort {
                    return Err(KernelError::SortMismatch {
                        expected: left_sort,
                        found: right_sort,
                    });
                }
                Ok(())
            }
            Prop::Pred(symbol, args) => {
                let expected = self
                    .predicates
                    .get(symbol)
                    .ok_or_else(|| KernelError::UnknownPredicate(symbol.clone()))?;
                if expected.len() != args.len() {
                    return Err(KernelError::ArityMismatch {
                        symbol: symbol.clone(),
                        expected: expected.len(),
                        found: args.len(),
                    });
                }
                for (arg, sort) in args.iter().zip(expected) {
                    let found = self.check_term_in(arg, scope)?;
                    if &found != sort {
                        return Err(KernelError::SortMismatch {
                            expected: sort.clone(),
                            found,
                        });
                    }
                }
                Ok(())
            }
        }
    }

    /// Looks up a declared axiom.
    pub fn axiom(&self, name: &str) -> Option<&Axiom> {
        self.axioms.get(name)
    }

    /// Looks up a checked theorem.
    pub fn theorem(&self, name: &str) -> Option<&Theorem> {
        self.theorems.get(name)
    }

    fn ensure_fresh(&self, name: &str) -> Result<()> {
        if self.axioms.contains_key(name) || self.theorems.contains_key(name) {
            Err(KernelError::DuplicateName(name.to_string()))
        } else {
            Ok(())
        }
    }
}

/// Checks that `symbol` occurs only as `symbol(a)` for a recursive argument `a`.
fn check_structural(symbol: &str, term: &Term, recursive: &[String]) -> Result<()> {
    match term {
        Term::Var(_) => Ok(()),
        Term::Fun(name, args) if name == symbol => match args.split_first() {
            Some((Term::Var(arg), rest)) if recursive.contains(arg) => rest
                .iter()
                .try_for_each(|extra| check_structural(symbol, extra, recursive)),
            _ => Err(KernelError::NotStructural(symbol.to_string())),
        },
        Term::Fun(_, args) => args
            .iter()
            .try_for_each(|arg| check_structural(symbol, arg, recursive)),
    }
}
