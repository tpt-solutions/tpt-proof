//! Weakest-precondition verification-condition generation (SPEC.md §3, Layer 2).
//!
//! A [`Function`] is a small imperative program with `requires` and `ensures`
//! clauses. [`generate`] turns each `ensures` clause into a [`Vc`]: the
//! `requires` clauses are the assumptions, and the goal is the weakest
//! precondition of the body for that postcondition.
//!
//! Loops use havoc-by-renaming instead of quantifiers. The state at a loop head
//! is arbitrary, so the variables the loop assigns are replaced by fresh
//! constants in the loop's side conditions. Each VC treats its free constants as
//! universally quantified, so this gives the right meaning without `forall`.
//!
//! The source language is a model of Rust, not Rust itself. Translation from
//! MIR (SPEC.md §5) is not built yet.

use std::collections::BTreeSet;

use crate::vc::{Expr, Sort, Vc};

/// A statement of the source language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// `var := value`.
    Assign {
        /// The variable assigned.
        var: String,
        /// The value assigned.
        value: Expr,
    },
    /// A proof obligation: the condition must hold on every path reaching here.
    Assert(Expr),
    /// A fact the verifier may use from here on.
    Assume(Expr),
    /// A conditional.
    If {
        /// The branch condition.
        cond: Expr,
        /// Taken when `cond` holds.
        then_branch: Vec<Stmt>,
        /// Taken when `cond` does not hold.
        else_branch: Vec<Stmt>,
    },
    /// A loop with an invariant that must hold on entry and be preserved.
    While {
        /// The loop condition.
        cond: Expr,
        /// The loop invariant.
        invariant: Expr,
        /// The loop body.
        body: Vec<Stmt>,
    },
}

/// A function to verify.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// Used in VC names.
    pub name: String,
    /// Every program variable, including parameters, with its sort.
    pub vars: Vec<(String, Sort)>,
    /// Preconditions, assumed on entry.
    pub requires: Vec<Expr>,
    /// The body.
    pub body: Vec<Stmt>,
    /// Postconditions. Each becomes its own VC.
    pub ensures: Vec<Expr>,
    /// Inclusive bounds `(var, min, max)` on integer variables. Each assignment
    /// to a bounded variable carries an obligation that the new value is in
    /// range. This models fixed-width overflow: a `u8` is `(x, 0, 255)`.
    pub ranges: Vec<(String, i64, i64)>,
}

/// Errors in the function, found before any VC is built.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WpError {
    /// An assignment to a variable not in `Function::vars`.
    UndeclaredVariable(String),
    /// A range on a variable that is not an integer.
    NotAnInteger(String),
    /// A range whose minimum exceeds its maximum.
    EmptyRange(String),
}

impl std::fmt::Display for WpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WpError::UndeclaredVariable(name) => {
                write!(f, "assignment to undeclared variable `{name}`")
            }
            WpError::NotAnInteger(name) => write!(f, "range given for non-integer `{name}`"),
            WpError::EmptyRange(name) => write!(f, "range for `{name}` is empty"),
        }
    }
}

impl std::error::Error for WpError {}

/// Generates one VC per postcondition.
pub fn generate(function: &Function) -> Result<Vec<Vc>, WpError> {
    let declared: BTreeSet<&str> = function.vars.iter().map(|(n, _)| n.as_str()).collect();
    check_assignments(&function.body, &declared)?;
    for (name, min, max) in &function.ranges {
        match function.vars.iter().find(|(n, _)| n == name) {
            None => return Err(WpError::UndeclaredVariable(name.clone())),
            Some((_, Sort::Bool)) => return Err(WpError::NotAnInteger(name.clone())),
            Some((_, Sort::Int)) if min > max => return Err(WpError::EmptyRange(name.clone())),
            Some((_, Sort::Int)) => {}
        }
    }

    let mut vcs = Vec::new();
    for (index, post) in function.ensures.iter().enumerate() {
        let mut generator = Generator {
            sorts: &function.vars,
            ranges: &function.ranges,
            fresh: Vec::new(),
            counter: 0,
        };
        let goal = generator.wp(&function.body, post.clone());
        let mut vars = function.vars.clone();
        vars.extend(generator.fresh);
        vcs.push(Vc {
            name: format!("{}: ensures #{}", function.name, index + 1),
            vars,
            assumptions: function.requires.clone(),
            goal,
        });
    }
    Ok(vcs)
}

fn check_assignments(stmts: &[Stmt], declared: &BTreeSet<&str>) -> Result<(), WpError> {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { var, .. } => {
                if !declared.contains(var.as_str()) {
                    return Err(WpError::UndeclaredVariable(var.clone()));
                }
            }
            Stmt::Assert(_) | Stmt::Assume(_) => {}
            Stmt::If {
                then_branch,
                else_branch,
                ..
            } => {
                check_assignments(then_branch, declared)?;
                check_assignments(else_branch, declared)?;
            }
            Stmt::While { body, .. } => check_assignments(body, declared)?,
        }
    }
    Ok(())
}

struct Generator<'a> {
    sorts: &'a [(String, Sort)],
    ranges: &'a [(String, i64, i64)],
    fresh: Vec<(String, Sort)>,
    counter: usize,
}

impl Generator<'_> {
    /// The weakest precondition of `stmts` for postcondition `post`.
    fn wp(&mut self, stmts: &[Stmt], post: Expr) -> Expr {
        stmts
            .iter()
            .rev()
            .fold(post, |post, stmt| self.stmt(stmt, post))
    }

    fn stmt(&mut self, stmt: &Stmt, post: Expr) -> Expr {
        match stmt {
            Stmt::Assign { var, value } => {
                let post = substitute(&post, var, value);
                match self.range_of(var) {
                    Some((min, max)) => and(in_range(value.clone(), min, max), post),
                    None => post,
                }
            }
            Stmt::Assert(cond) => and(cond.clone(), post),
            Stmt::Assume(cond) => implies(cond.clone(), post),
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let then_wp = self.wp(then_branch, post.clone());
                let else_wp = self.wp(else_branch, post);
                and(
                    implies(cond.clone(), then_wp),
                    implies(not(cond.clone()), else_wp),
                )
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                let modified = modified_vars(body);
                let body_wp = self.wp(body, invariant.clone());
                let preserve = implies(and(invariant.clone(), cond.clone()), body_wp);
                let exit = implies(and(invariant.clone(), not(cond.clone())), post);
                let preserve = self.havoc(preserve, &modified);
                let exit = self.havoc(exit, &modified);
                and(invariant.clone(), and(preserve, exit))
            }
        }
    }

    fn range_of(&self, var: &str) -> Option<(i64, i64)> {
        self.ranges
            .iter()
            .find(|(name, _, _)| name == var)
            .map(|(_, min, max)| (*min, *max))
    }

    /// Replaces each variable in `vars` by a fresh constant. The constant is
    /// free in the VC, so the VC holds for every value it could take. A
    /// havoced bounded variable is still in range at the loop head, so those
    /// range facts are assumed.
    fn havoc(&mut self, expr: Expr, vars: &BTreeSet<String>) -> Expr {
        let mut expr = expr;
        let mut facts = Vec::new();
        for var in vars {
            self.counter += 1;
            let fresh = format!("__h{}", self.counter);
            let sort = self
                .sorts
                .iter()
                .find(|(name, _)| name == var)
                .map(|(_, sort)| *sort)
                .expect("assignments are checked against the declared variables");
            if let Some((min, max)) = self.range_of(var) {
                facts.push(in_range(Expr::Var(fresh.clone()), min, max));
            }
            self.fresh.push((fresh.clone(), sort));
            expr = substitute(&expr, var, &Expr::Var(fresh));
        }
        if facts.is_empty() {
            expr
        } else {
            implies(Expr::And(facts), expr)
        }
    }
}

/// Every variable assigned anywhere in `stmts`.
fn modified_vars(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    collect_modified(stmts, &mut out);
    out
}

fn collect_modified(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { var, .. } => {
                out.insert(var.clone());
            }
            Stmt::Assert(_) | Stmt::Assume(_) => {}
            Stmt::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_modified(then_branch, out);
                collect_modified(else_branch, out);
            }
            Stmt::While { body, .. } => collect_modified(body, out),
        }
    }
}

/// Replaces every occurrence of variable `name` in `expr` by `replacement`.
/// Expressions have no binders, so no capture check is needed.
fn substitute(expr: &Expr, name: &str, replacement: &Expr) -> Expr {
    let go = |e: &Expr| substitute(e, name, replacement);
    let boxed = |e: &Expr| Box::new(go(e));
    match expr {
        Expr::Var(v) if v == name => replacement.clone(),
        Expr::Var(_) | Expr::Int(_) | Expr::Bool(_) => expr.clone(),
        Expr::Add(a, b) => Expr::Add(boxed(a), boxed(b)),
        Expr::Sub(a, b) => Expr::Sub(boxed(a), boxed(b)),
        Expr::Lt(a, b) => Expr::Lt(boxed(a), boxed(b)),
        Expr::Le(a, b) => Expr::Le(boxed(a), boxed(b)),
        Expr::Eq(a, b) => Expr::Eq(boxed(a), boxed(b)),
        Expr::Not(a) => Expr::Not(boxed(a)),
        Expr::And(items) => Expr::And(items.iter().map(go).collect()),
        Expr::Or(items) => Expr::Or(items.iter().map(go).collect()),
        Expr::Implies(a, b) => Expr::Implies(boxed(a), boxed(b)),
    }
}

/// `min <= value && value <= max`.
fn in_range(value: Expr, min: i64, max: i64) -> Expr {
    Expr::And(vec![
        Expr::Le(Box::new(Expr::Int(min)), Box::new(value.clone())),
        Expr::Le(Box::new(value), Box::new(Expr::Int(max))),
    ])
}

fn and(a: Expr, b: Expr) -> Expr {
    Expr::And(vec![a, b])
}

fn implies(a: Expr, b: Expr) -> Expr {
    Expr::Implies(Box::new(a), Box::new(b))
}

fn not(a: Expr) -> Expr {
    Expr::Not(Box::new(a))
}
