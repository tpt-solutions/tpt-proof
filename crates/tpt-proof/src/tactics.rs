//! Layer 3: an interactive proof framework (spec.txt §6, Principle 3).
//!
//! A [`Proof`] holds a tree of goals. Each tactic closes or splits the first open
//! goal, and records how to build the proof term for it from its subproofs. The
//! tactics are untrusted. They can be wrong, and a wrong tactic only produces a
//! term the kernel rejects. [`Proof::qed`] assembles the complete term and asks
//! the kernel to check it against the statement, which is the only step that
//! produces a [`Theorem`].

use std::fmt;

use tpt_proof_kernel::formula::{self, Formula};
use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term, Theorem};

/// A proposition to prove, together with the hypotheses available to prove it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Goal {
    /// Named hypotheses in scope, oldest first.
    pub hyps: Vec<(String, Prop)>,
    /// The proposition still to be proved.
    pub target: Prop,
}

impl fmt::Display for Goal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, prop) in &self.hyps {
            writeln!(f, "{name} : {prop}")?;
        }
        write!(f, "⊢ {}", self.target)
    }
}

/// A tactic that may apply to the current goal. See [`Proof::suggestions`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Suggestion {
    /// `intro`, for a goal `A -> B`. The name is chosen by the user.
    Intro,
    /// `intro_forall`, for a goal `forall p. B`. The name is chosen by the user.
    IntroForall,
    /// `assumption`, when a hypothesis matches the goal exactly.
    Assumption,
    /// `apply_hyp name`, when hypothesis `name` concludes the goal.
    ApplyHyp(String),
    /// `apply_axiom name`, when a declared axiom concludes the goal.
    ApplyAxiom(String),
    /// `apply_theorem name`, when a checked theorem concludes the goal.
    ApplyTheorem(String),
    /// `case_split`, for a goal `forall x:T. P` where `T` is an inductive sort.
    CaseSplit,
    /// `induct`, for a goal `forall x:T. P` where `T` is an inductive sort.
    Induct,
}

impl fmt::Display for Suggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Suggestion::Intro => write!(f, "intro <name>"),
            Suggestion::IntroForall => write!(f, "intro_forall <name>"),
            Suggestion::Assumption => write!(f, "assumption"),
            Suggestion::ApplyHyp(name) => write!(f, "apply_hyp {name}"),
            Suggestion::ApplyAxiom(name) => write!(f, "apply_axiom {name}"),
            Suggestion::ApplyTheorem(name) => write!(f, "apply_theorem {name}"),
            Suggestion::CaseSplit => write!(f, "case_split"),
            Suggestion::Induct => write!(f, "induct"),
        }
    }
}

/// Whether `prop` is an implication whose conclusion is `target`.
fn concludes(prop: &Prop, target: &Prop) -> bool {
    matches!(prop, Prop::Imp(_, conclusion) if conclusion.alpha_eq(target))
}

/// Why a tactic could not be applied to a goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticError {
    /// There are no open goals left.
    NoGoals,
    /// `intro` needs an implication.
    NotAnImplication(Prop),
    /// `intro_forall` needs a universal quantifier.
    NotAForall(Prop),
    /// A named hypothesis is not in scope.
    NoSuchHypothesis(String),
    /// A named axiom is not declared.
    NoSuchAxiom(String),
    /// A named theorem is not declared.
    NoSuchTheorem(String),
    /// The tactic's conclusion is not the goal's target.
    TargetMismatch {
        /// The goal's target.
        expected: Prop,
        /// The conclusion the tactic would prove.
        found: Prop,
    },
    /// No hypothesis proves the target.
    NoMatchingHypothesis,
    /// Renaming the bound variable would capture a free name in the target.
    NameClash(String),
    /// `case_split` needs a universal quantifier over individuals.
    NotAnIndividualForall(Prop),
    /// `case_split` needs the quantified sort to be inductive.
    NotInductive(Sort),
    /// `case_split` on a variable that a hypothesis mentions would make the
    /// split unsound, because the hypothesis refers to one particular value.
    VariableInHypothesis(String),
    /// `tauto` needs the goal and every hypothesis to be built from implications,
    /// `false` and atoms.
    NotPropositional(Prop),
    /// `rewrite` needs an equation.
    NotAnEquation(Prop),
    /// `rewrite` finds no occurrence of the equation's left-hand side in the goal.
    RewriteTargetNotFound(Term),
    /// The left-hand side depends on a variable that the goal binds, so it cannot be
    /// abstracted out of the goal.
    RewriteUnsafe(Term),
}

impl fmt::Display for TacticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TacticError::NoGoals => write!(f, "there are no open goals"),
            TacticError::NotAnImplication(p) => {
                write!(f, "`intro` needs an implication, found {p}")
            }
            TacticError::NotPropositional(p) => write!(
                f,
                "`tauto` needs implications, `false` and atoms, found {p}"
            ),
            TacticError::NotAForall(p) => write!(f, "`intro_forall` needs a forall, found {p}"),
            TacticError::NoSuchHypothesis(n) => write!(f, "no hypothesis named `{n}`"),
            TacticError::NoSuchAxiom(n) => write!(f, "no axiom named `{n}`"),
            TacticError::NoSuchTheorem(n) => write!(f, "no theorem named `{n}`"),
            TacticError::TargetMismatch { expected, found } => {
                write!(f, "tactic proves {found}, but the goal is {expected}")
            }
            TacticError::NoMatchingHypothesis => write!(f, "no hypothesis matches the goal"),
            TacticError::NameClash(n) => write!(f, "`{n}` is already free in the target"),
            TacticError::NotAnIndividualForall(p) => {
                write!(f, "`case_split` needs a forall over individuals, found {p}")
            }
            TacticError::NotInductive(sort) => {
                write!(
                    f,
                    "`case_split` needs an inductive sort, `{sort}` is not one"
                )
            }
            TacticError::VariableInHypothesis(n) => {
                write!(
                    f,
                    "`{n}` is mentioned by a hypothesis, so it cannot be split"
                )
            }
            TacticError::NotAnEquation(p) => write!(f, "`rewrite` needs an equation, found {p}"),
            TacticError::RewriteTargetNotFound(t) => {
                write!(f, "`rewrite` finds no occurrence of {t} in the goal")
            }
            TacticError::RewriteUnsafe(t) => write!(
                f,
                "{t} depends on a variable the goal binds, so it cannot be rewritten"
            ),
        }
    }
}

impl std::error::Error for TacticError {}

/// Why [`Proof::qed`] failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofError {
    /// Goals remain open. The count is given.
    OpenGoals(usize),
    /// The kernel rejected the assembled proof term.
    Kernel(KernelError),
}

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofError::OpenGoals(n) => write!(f, "{n} goal(s) remain open"),
            ProofError::Kernel(err) => write!(f, "the kernel rejected the proof: {err}"),
        }
    }
}

impl std::error::Error for ProofError {}

impl From<KernelError> for ProofError {
    fn from(err: KernelError) -> Self {
        ProofError::Kernel(err)
    }
}

/// How a tactic splits a goal: the subgoals it produces, and how to build the
/// proof term for the goal from proofs of the subgoals.
pub struct Step {
    subgoals: Vec<Goal>,
    build: Box<dyn FnOnce(Vec<ProofTerm>) -> ProofTerm>,
}

enum Tree {
    Open(Goal),
    Node {
        build: Box<dyn FnOnce(Vec<ProofTerm>) -> ProofTerm>,
        children: Vec<Tree>,
    },
}

/// An interactive proof of `target` against a kernel.
pub struct Proof<'k> {
    kernel: &'k Kernel,
    target: Prop,
    tree: Tree,
}

impl<'k> Proof<'k> {
    /// Starts a proof of `target` with no hypotheses.
    pub fn new(kernel: &'k Kernel, target: Prop) -> Self {
        let tree = Tree::Open(Goal {
            hyps: Vec::new(),
            target: target.clone(),
        });
        Proof {
            kernel,
            target,
            tree,
        }
    }

    /// All open goals, in the order they will be proved.
    pub fn goals(&self) -> Vec<Goal> {
        let mut out = Vec::new();
        collect_open(&self.tree, &mut out);
        out
    }

    /// `intro name`: from `A -> B`, adds `name : A` and leaves `B`.
    pub fn intro(&mut self, name: &str) -> Result<(), TacticError> {
        self.apply(|goal| intro(goal, name))
    }

    /// `intro_forall name`: from `forall p. B`, leaves `B` with `p` renamed to `name`.
    pub fn intro_forall(&mut self, name: &str) -> Result<(), TacticError> {
        self.apply(|goal| intro_forall(goal, name))
    }

    /// `intro_individual name`: from `forall x:S. B`, leaves `B` with `x` renamed
    /// to `name`. The name must not be free in the target, and no hypothesis may
    /// mention it, so that the new binder cannot capture anything.
    pub fn intro_individual(&mut self, name: &str) -> Result<(), TacticError> {
        self.apply(|goal| intro_individual(goal, name))
    }

    /// `tauto`: closes the goal when the hypotheses imply the target in every
    /// truth assignment. The goal and the hypotheses must be built from
    /// implications, `false` and atoms. The tautology rule decides the statement,
    /// and each hypothesis is then applied in order.
    pub fn tauto(&mut self) -> Result<(), TacticError> {
        self.apply(tauto)
    }

    /// Closes the goal with a hypothesis of the same proposition.
    pub fn assumption(&mut self) -> Result<(), TacticError> {
        self.apply(assumption)
    }

    /// Applies hypothesis `name : A -> B` to a goal `B`, leaving `A`.
    pub fn apply_hyp(&mut self, name: &str) -> Result<(), TacticError> {
        let prop = {
            let goal = self.focus()?;
            goal.hyps
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, p)| p.clone())
                .ok_or_else(|| TacticError::NoSuchHypothesis(name.to_string()))?
        };
        self.apply(|goal| apply_term(goal, ProofTerm::Var(name.to_string()), prop))
    }

    /// Applies a declared axiom `A -> B` to a goal `B`, leaving `A`.
    pub fn apply_axiom(&mut self, name: &str) -> Result<(), TacticError> {
        let axiom = self
            .kernel
            .axiom(name)
            .ok_or_else(|| TacticError::NoSuchAxiom(name.to_string()))?;
        let prop = axiom.prop.clone();
        self.apply(|goal| apply_term(goal, ProofTerm::Axiom(name.to_string()), prop))
    }

    /// Applies a checked theorem `A -> B` to a goal `B`, leaving `A`.
    pub fn apply_theorem(&mut self, name: &str) -> Result<(), TacticError> {
        let theorem = self
            .kernel
            .theorem(name)
            .ok_or_else(|| TacticError::NoSuchTheorem(name.to_string()))?;
        let prop = theorem.prop().clone();
        self.apply(|goal| apply_term(goal, ProofTerm::Const(name.to_string()), prop))
    }

    /// Closes the goal with the given proof term. The kernel checks it at
    /// [`Proof::qed`], so a wrong term fails there.
    pub fn exact(&mut self, term: ProofTerm) -> Result<(), TacticError> {
        self.apply(|_| {
            Ok(Step {
                subgoals: Vec::new(),
                build: Box::new(move |_| term),
            })
        })
    }

    /// `case_split`: from a goal `forall x:T. P` with `T` inductive, leaves one
    /// goal per constructor `C`, namely `forall a0..an. P[x := C(a0..an)]`.
    pub fn case_split(&mut self) -> Result<(), TacticError> {
        let kernel = self.kernel;
        self.apply(|goal| case_split(kernel, goal))
    }

    /// `induct`: from a goal `forall x:T. P` with `T` inductive, leaves one goal
    /// per constructor `C`, namely `forall a0..an. (P[x := aj] for each recursive
    /// aj) -> P[x := C(a0..an)]`. The hypotheses are part of the target, so each
    /// case is closed by introducing the arguments with `intro_individual`, the
    /// hypotheses with `intro`, and then the conclusion.
    pub fn induct(&mut self) -> Result<(), TacticError> {
        let kernel = self.kernel;
        self.apply(|goal| induct(kernel, goal))
    }

    /// `rewrite_hyp name`: rewrites the goal with hypothesis `name : l = r`. The
    /// occurrences of `l` in the goal become `r`, and the new goal is the
    /// goal with `r` in their place.
    pub fn rewrite_hyp(&mut self, name: &str) -> Result<(), TacticError> {
        let prop = {
            let goal = self.focus()?;
            goal.hyps
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, p)| p.clone())
                .ok_or_else(|| TacticError::NoSuchHypothesis(name.to_string()))?
        };
        self.apply(|goal| rewrite(goal, &prop, ProofTerm::Var(name.to_string())))
    }

    /// `rewrite_axiom name`: as [`Proof::rewrite_hyp`], with a declared axiom.
    pub fn rewrite_axiom(&mut self, name: &str) -> Result<(), TacticError> {
        let prop = self
            .kernel
            .axiom(name)
            .ok_or_else(|| TacticError::NoSuchAxiom(name.to_string()))?
            .prop
            .clone();
        self.apply(|goal| rewrite(goal, &prop, ProofTerm::Axiom(name.to_string())))
    }

    /// `rewrite_theorem name`: as [`Proof::rewrite_hyp`], with a checked theorem.
    pub fn rewrite_theorem(&mut self, name: &str) -> Result<(), TacticError> {
        let prop = self
            .kernel
            .theorem(name)
            .ok_or_else(|| TacticError::NoSuchTheorem(name.to_string()))?
            .prop()
            .clone();
        self.apply(|goal| rewrite(goal, &prop, ProofTerm::Const(name.to_string())))
    }

    /// Finishes the proof. It fails if goals remain open or the kernel rejects
    /// the assembled term. On success the theorem is returned.
    pub fn qed(self) -> Result<Theorem, ProofError> {
        let mut open = Vec::new();
        collect_open(&self.tree, &mut open);
        if !open.is_empty() {
            return Err(ProofError::OpenGoals(open.len()));
        }
        let term = assemble(self.tree).expect("no open goals remain");
        Ok(self.kernel.check_proof(&term, &self.target)?)
    }

    /// The tactics that apply to the first open goal, most direct first. Each
    /// one is a call that [`Proof`] would accept. This is advice only: nothing
    /// is applied, and the kernel still decides at [`Proof::qed`].
    pub fn suggestions(&self) -> Vec<Suggestion> {
        let Ok(goal) = self.focus() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        match &goal.target {
            Prop::Imp(_, _) => out.push(Suggestion::Intro),
            Prop::Forall(_, _) => out.push(Suggestion::IntroForall),
            Prop::ForallInd(_, sort, _) if self.kernel.constructors(sort).is_some() => {
                out.push(Suggestion::CaseSplit);
                out.push(Suggestion::Induct);
            }
            _ => {}
        }
        if goal
            .hyps
            .iter()
            .any(|(_, prop)| prop.alpha_eq(&goal.target))
        {
            out.push(Suggestion::Assumption);
        }
        for (name, prop) in goal.hyps.iter().rev() {
            if concludes(prop, &goal.target) {
                out.push(Suggestion::ApplyHyp(name.clone()));
            }
        }
        for axiom in self.kernel.axioms() {
            if concludes(&axiom.prop, &goal.target) {
                out.push(Suggestion::ApplyAxiom(axiom.name.clone()));
            }
        }
        for (name, theorem) in self.kernel.theorems() {
            if concludes(theorem.prop(), &goal.target) {
                out.push(Suggestion::ApplyTheorem(name.to_string()));
            }
        }
        out
    }

    fn focus(&self) -> Result<Goal, TacticError> {
        self.goals().into_iter().next().ok_or(TacticError::NoGoals)
    }

    fn apply<F>(&mut self, tactic: F) -> Result<(), TacticError>
    where
        F: FnOnce(&Goal) -> Result<Step, TacticError>,
    {
        let slot = first_open_mut(&mut self.tree).ok_or(TacticError::NoGoals)?;
        let goal = match slot {
            Tree::Open(goal) => goal.clone(),
            Tree::Node { .. } => unreachable!("first_open_mut returns an open goal"),
        };
        let step = tactic(&goal)?;
        *slot = Tree::Node {
            build: step.build,
            children: step.subgoals.into_iter().map(Tree::Open).collect(),
        };
        Ok(())
    }
}

fn intro(goal: &Goal, name: &str) -> Result<Step, TacticError> {
    let Prop::Imp(domain, codomain) = &goal.target else {
        return Err(TacticError::NotAnImplication(goal.target.clone()));
    };
    let mut hyps = goal.hyps.clone();
    hyps.push((name.to_string(), (**domain).clone()));
    let subgoal = Goal {
        hyps,
        target: (**codomain).clone(),
    };
    let binder = name.to_string();
    let domain = (**domain).clone();
    Ok(Step {
        subgoals: vec![subgoal],
        build: Box::new(move |mut kids| ProofTerm::Lam(binder, domain, Box::new(kids.remove(0)))),
    })
}

fn intro_forall(goal: &Goal, name: &str) -> Result<Step, TacticError> {
    let Prop::Forall(bound, body) = &goal.target else {
        return Err(TacticError::NotAForall(goal.target.clone()));
    };
    // Renaming `bound` to `name` is only safe if `name` is not already free in
    // the body, unless it is the bound name itself.
    if name != bound && body.has_free(name) {
        return Err(TacticError::NameClash(name.to_string()));
    }
    let target = body.substitute(bound, &Prop::atom(name));
    let subgoal = Goal {
        hyps: goal.hyps.clone(),
        target,
    };
    let binder = name.to_string();
    Ok(Step {
        subgoals: vec![subgoal],
        build: Box::new(move |mut kids| ProofTerm::TyLam(binder, Box::new(kids.remove(0)))),
    })
}

/// The formula that stands for a propositional proposition, or `None` if the
/// proposition uses a quantifier, an equation or a predicate.
fn to_formula(prop: &Prop) -> Option<Formula> {
    match prop {
        Prop::Atom(name) if name == formula::FALSE => Some(Formula::Const(false)),
        Prop::Atom(_) => Some(Formula::Atom(prop.clone())),
        Prop::Imp(a, b) => Some(Formula::Imp(
            Box::new(to_formula(a)?),
            Box::new(to_formula(b)?),
        )),
        _ => None,
    }
}

fn tauto(goal: &Goal) -> Result<Step, TacticError> {
    let not_propositional = |prop: &Prop| TacticError::NotPropositional(prop.clone());
    let mut whole = to_formula(&goal.target).ok_or_else(|| not_propositional(&goal.target))?;
    // `H1 -> ... -> Hn -> target`, with the hypotheses in order, oldest outermost.
    for (_, prop) in goal.hyps.iter().rev() {
        let hyp = to_formula(prop).ok_or_else(|| not_propositional(prop))?;
        whole = Formula::Imp(Box::new(hyp), Box::new(whole));
    }
    let term = goal
        .hyps
        .iter()
        .fold(ProofTerm::Taut(whole), |term, (name, _)| {
            ProofTerm::App(Box::new(term), Box::new(ProofTerm::Var(name.clone())))
        });
    Ok(Step {
        subgoals: Vec::new(),
        build: Box::new(move |_| term),
    })
}

fn assumption(goal: &Goal) -> Result<Step, TacticError> {
    let (name, _) = goal
        .hyps
        .iter()
        .rev()
        .find(|(_, prop)| prop.alpha_eq(&goal.target))
        .ok_or(TacticError::NoMatchingHypothesis)?;
    let term = ProofTerm::Var(name.clone());
    Ok(Step {
        subgoals: Vec::new(),
        build: Box::new(move |_| term),
    })
}

/// Shared logic for `apply_*`: `term` has type `prop`, which must be `A -> goal`.
fn apply_term(goal: &Goal, term: ProofTerm, prop: Prop) -> Result<Step, TacticError> {
    let Prop::Imp(premise, conclusion) = prop else {
        return Err(TacticError::NotAnImplication(prop));
    };
    if !conclusion.alpha_eq(&goal.target) {
        return Err(TacticError::TargetMismatch {
            expected: goal.target.clone(),
            found: *conclusion,
        });
    }
    let subgoal = Goal {
        hyps: goal.hyps.clone(),
        target: *premise,
    };
    Ok(Step {
        subgoals: vec![subgoal],
        build: Box::new(move |mut kids| ProofTerm::App(Box::new(term), Box::new(kids.remove(0)))),
    })
}

fn intro_individual(goal: &Goal, name: &str) -> Result<Step, TacticError> {
    let Prop::ForallInd(bound, sort, body) = &goal.target else {
        return Err(TacticError::NotAnIndividualForall(goal.target.clone()));
    };
    if name != bound && body.has_free_individual(name) {
        return Err(TacticError::NameClash(name.to_string()));
    }
    if goal
        .hyps
        .iter()
        .any(|(_, prop)| prop.has_free_individual(name))
    {
        return Err(TacticError::VariableInHypothesis(name.to_string()));
    }
    let subgoal = Goal {
        hyps: goal.hyps.clone(),
        target: body.subst_individual(bound, &Term::var(name)),
    };
    let binder = name.to_string();
    let sort = sort.clone();
    Ok(Step {
        subgoals: vec![subgoal],
        build: Box::new(move |mut kids| ProofTerm::IndLam(binder, sort, Box::new(kids.remove(0)))),
    })
}

fn case_split(kernel: &Kernel, goal: &Goal) -> Result<Step, TacticError> {
    split(kernel, goal, false)
}

fn induct(kernel: &Kernel, goal: &Goal) -> Result<Step, TacticError> {
    split(kernel, goal, true)
}

/// Splits a goal `forall x:T. P` over an inductive sort `T`: one subgoal per
/// constructor, from [`Kernel::case_premise`], or from
/// [`Kernel::induction_premise`] when `induction` is set.
fn split(kernel: &Kernel, goal: &Goal, induction: bool) -> Result<Step, TacticError> {
    let Prop::ForallInd(variable, sort, motive) = &goal.target else {
        return Err(TacticError::NotAnIndividualForall(goal.target.clone()));
    };
    let constructors = kernel
        .constructors(sort)
        .ok_or_else(|| TacticError::NotInductive(sort.clone()))?;
    if goal
        .hyps
        .iter()
        .any(|(_, prop)| prop.has_free_individual(variable))
    {
        return Err(TacticError::VariableInHypothesis(variable.clone()));
    }
    let mut subgoals = Vec::new();
    for (constructor, _) in constructors {
        let premise = if induction {
            kernel.induction_premise(variable, sort, motive, constructor)
        } else {
            kernel.case_premise(variable, sort, motive, constructor)
        };
        let target = premise.map_err(|_| TacticError::NotInductive(sort.clone()))?;
        subgoals.push(Goal {
            hyps: goal.hyps.clone(),
            target,
        });
    }
    let variable = variable.clone();
    let sort = sort.clone();
    let motive = (**motive).clone();
    Ok(Step {
        subgoals,
        build: Box::new(move |kids| {
            if induction {
                ProofTerm::Induct(variable, sort, motive, kids)
            } else {
                ProofTerm::Cases(variable, sort, motive, kids)
            }
        }),
    })
}

/// Rewrites the goal with `equation : l = r` (proved by `proof`): the new goal has
/// `r` where the goal has `l`, and the proof builds the old goal back with
/// Leibniz substitution on the symmetric equation `r = l`.
fn rewrite(goal: &Goal, equation: &Prop, proof: ProofTerm) -> Result<Step, TacticError> {
    let Prop::Eq(lhs, rhs) = equation else {
        return Err(TacticError::NotAnEquation(equation.clone()));
    };
    let variable = fresh_variable(goal, &[lhs, rhs]);
    let (motive, found) = abstract_term(&goal.target, lhs, &variable)
        .ok_or_else(|| TacticError::RewriteUnsafe(lhs.clone()))?;
    if !found {
        return Err(TacticError::RewriteTargetNotFound(lhs.clone()));
    }
    let subgoal = Goal {
        hyps: goal.hyps.clone(),
        target: motive.subst_individual(&variable, rhs),
    };
    let symmetric = ProofTerm::Sym(Box::new(proof));
    Ok(Step {
        subgoals: vec![subgoal],
        build: Box::new(move |mut kids| {
            ProofTerm::Leibniz(
                variable,
                motive,
                Box::new(symmetric),
                Box::new(kids.remove(0)),
            )
        }),
    })
}

/// Replaces every occurrence of `term` in `prop` by the variable `var`. Returns the
/// abstracted proposition and whether anything was replaced. `None` when an
/// occurrence sits under a binder that `term` depends on, since the same name
/// would then denote a different value there.
fn abstract_term(prop: &Prop, term: &Term, var: &str) -> Option<(Prop, bool)> {
    Some(match prop {
        Prop::Atom(name) => (Prop::Atom(name.clone()), false),
        Prop::Imp(a, b) => {
            let (a, found_a) = abstract_term(a, term, var)?;
            let (b, found_b) = abstract_term(b, term, var)?;
            (Prop::imp(a, b), found_a || found_b)
        }
        Prop::Forall(name, body) => {
            let (body, found) = abstract_term(body, term, var)?;
            (Prop::forall(name, body), found)
        }
        Prop::ForallInd(name, sort, body) => {
            let (body, found) = abstract_term(body, term, var)?;
            if found && term_vars(term).contains(name) {
                return None;
            }
            (Prop::forall_sorted(name, sort.clone(), body), found)
        }
        Prop::Eq(left, right) => {
            let (left, found_left) = replace_term(left, term, var);
            let (right, found_right) = replace_term(right, term, var);
            (Prop::Eq(left, right), found_left || found_right)
        }
        Prop::Pred(symbol, args) => {
            let mut found = false;
            let args = args
                .iter()
                .map(|arg| {
                    let (arg, hit) = replace_term(arg, term, var);
                    found |= hit;
                    arg
                })
                .collect();
            (Prop::Pred(symbol.clone(), args), found)
        }
    })
}

fn replace_term(term: &Term, target: &Term, var: &str) -> (Term, bool) {
    if term == target {
        return (Term::var(var), true);
    }
    match term {
        Term::Var(_) => (term.clone(), false),
        Term::Fun(symbol, args) => {
            let mut found = false;
            let args = args
                .iter()
                .map(|arg| {
                    let (arg, hit) = replace_term(arg, target, var);
                    found |= hit;
                    arg
                })
                .collect();
            (Term::app(symbol, args), found)
        }
    }
}

/// The individual variables a term mentions.
fn term_vars(term: &Term) -> Vec<String> {
    match term {
        Term::Var(name) => vec![name.clone()],
        Term::Fun(_, args) => args.iter().flat_map(term_vars).collect(),
    }
}

/// Every individual name that a proposition mentions, bound or free.
fn names_in(prop: &Prop, out: &mut Vec<String>) {
    match prop {
        Prop::Atom(_) => {}
        Prop::Imp(a, b) => {
            names_in(a, out);
            names_in(b, out);
        }
        Prop::Forall(_, body) => names_in(body, out),
        Prop::ForallInd(name, _, body) => {
            out.push(name.clone());
            names_in(body, out);
        }
        Prop::Eq(left, right) => {
            out.extend(term_vars(left));
            out.extend(term_vars(right));
        }
        Prop::Pred(_, args) => out.extend(args.iter().flat_map(term_vars)),
    }
}

/// A name for a new individual variable that no hypothesis, the target, or the
/// given terms use, so that the abstraction cannot be captured.
fn fresh_variable(goal: &Goal, terms: &[&Term]) -> String {
    let mut taken = Vec::new();
    names_in(&goal.target, &mut taken);
    for (_, prop) in &goal.hyps {
        names_in(prop, &mut taken);
    }
    for term in terms {
        taken.extend(term_vars(term));
    }
    let mut name = "x".to_string();
    while taken.contains(&name) {
        name.push('\'');
    }
    name
}

fn collect_open(tree: &Tree, out: &mut Vec<Goal>) {
    match tree {
        Tree::Open(goal) => out.push(goal.clone()),
        Tree::Node { children, .. } => {
            for child in children {
                collect_open(child, out);
            }
        }
    }
}

fn first_open_mut(tree: &mut Tree) -> Option<&mut Tree> {
    if matches!(*tree, Tree::Open(_)) {
        return Some(tree);
    }
    match tree {
        Tree::Node { children, .. } => children.iter_mut().find_map(first_open_mut),
        Tree::Open(_) => None,
    }
}

fn assemble(tree: Tree) -> Option<ProofTerm> {
    match tree {
        Tree::Open(_) => None,
        Tree::Node { build, children } => {
            let kids = children
                .into_iter()
                .map(assemble)
                .collect::<Option<Vec<_>>>()?;
            Some(build(kids))
        }
    }
}
