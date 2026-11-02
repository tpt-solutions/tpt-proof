//! Layer 3: an interactive proof framework (spec.txt §6, Principle 3).
//!
//! A [`Proof`] holds a tree of goals. Each tactic closes or splits the first open
//! goal, and records how to build the proof term for it from its subproofs. The
//! tactics are untrusted. They can be wrong, and a wrong tactic only produces a
//! term the kernel rejects. [`Proof::qed`] assembles the complete term and asks
//! the kernel to check it against the statement, which is the only step that
//! produces a [`Theorem`].

use std::fmt;

use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Theorem};

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
}

impl fmt::Display for TacticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TacticError::NoGoals => write!(f, "there are no open goals"),
            TacticError::NotAnImplication(p) => {
                write!(f, "`intro` needs an implication, found {p}")
            }
            TacticError::NotAForall(p) => write!(f, "`intro_forall` needs a forall, found {p}"),
            TacticError::NoSuchHypothesis(n) => write!(f, "no hypothesis named `{n}`"),
            TacticError::NoSuchAxiom(n) => write!(f, "no axiom named `{n}`"),
            TacticError::NoSuchTheorem(n) => write!(f, "no theorem named `{n}`"),
            TacticError::TargetMismatch { expected, found } => {
                write!(f, "tactic proves {found}, but the goal is {expected}")
            }
            TacticError::NoMatchingHypothesis => write!(f, "no hypothesis matches the goal"),
            TacticError::NameClash(n) => write!(f, "`{n}` is already free in the target"),
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
