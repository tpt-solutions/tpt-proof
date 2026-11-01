//! Verification conditions: the logical formulas a function's contract reduces to.
//!
//! This is a small first-order language over integers and booleans. Translation
//! from Rust MIR (spec.txt §5) is not built yet, so VCs are constructed by hand
//! for now.

/// The sort (type) of a variable in a verification condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    /// Mathematical integers.
    Int,
    /// Booleans.
    Bool,
}

/// A formula or term. Integer and boolean terms share one type; [`crate::smt`]
/// sort-checks them before anything reaches the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// An integer literal.
    Int(i64),
    /// A boolean literal.
    Bool(bool),
    /// A declared variable.
    Var(String),
    /// Integer addition.
    Add(Box<Expr>, Box<Expr>),
    /// Integer subtraction.
    Sub(Box<Expr>, Box<Expr>),
    /// Integer multiplication. Non-linear terms are harder for the solver; it may
    /// answer `unknown` for them.
    Mul(Box<Expr>, Box<Expr>),
    /// Integer division, rounding toward zero for non-negative operands. Signed
    /// division needs different rounding, so the translator does not produce it.
    Div(Box<Expr>, Box<Expr>),
    /// Integer remainder, for non-negative operands. See [`Expr::Div`].
    Rem(Box<Expr>, Box<Expr>),
    /// A conditional: `if cond then a else b`. Both branches have the same sort.
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Integer less-than.
    Lt(Box<Expr>, Box<Expr>),
    /// Integer less-than-or-equal.
    Le(Box<Expr>, Box<Expr>),
    /// Equality of two terms of the same sort.
    Eq(Box<Expr>, Box<Expr>),
    /// Boolean negation.
    Not(Box<Expr>),
    /// Conjunction of any number of formulas.
    And(Vec<Expr>),
    /// Disjunction of any number of formulas.
    Or(Vec<Expr>),
    /// Implication.
    Implies(Box<Expr>, Box<Expr>),
}

/// A verification condition: under the declared variables and the assumptions,
/// the goal must hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Vc {
    /// A label for reports, such as `insert: ensures len <= MAX`.
    pub name: String,
    /// Declared variables and their sorts.
    pub vars: Vec<(String, Sort)>,
    /// Facts the goal may use.
    pub assumptions: Vec<Expr>,
    /// The formula to prove.
    pub goal: Expr,
}
