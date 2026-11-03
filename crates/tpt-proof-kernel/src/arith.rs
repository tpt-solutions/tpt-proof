//! Built-in integer arithmetic.
//!
//! The sort `Int`, the operations `+`, `-`, `*` and `neg`, and the predicates
//! `<=` and `<` are declared by [`crate::Kernel::new`] with their usual
//! meaning. A numeral is a symbol spelling a non-negative integer in decimal,
//! without leading zeros, and denotes that integer. These names cannot be
//! declared again.
//!
//! The meaning matters in one place: the tautology rule evaluates ground atoms
//! (atoms with no variables and no other symbols) with it. Every other symbol
//! is uninterpreted. An overflow is not an error: the atom is then treated as
//! an unknown letter, which can only make the rule reject more.

use crate::terms::{Prop, Term};

/// The name of the integer sort.
pub const INT: &str = "Int";

/// Whether `symbol` spells a numeral in canonical decimal form.
pub(crate) fn is_numeral(symbol: &str) -> bool {
    !symbol.is_empty()
        && symbol.bytes().all(|b| b.is_ascii_digit())
        && (symbol == "0" || !symbol.starts_with('0'))
}

/// Whether `symbol` is a built-in name. User declarations cannot reuse it, and
/// binders cannot bind it: `false` is the constant false to the tautology rule,
/// and `#r` is the variable the encodings of `and` and `or` bind.
pub(crate) fn is_reserved(symbol: &str) -> bool {
    is_numeral(symbol) || symbol == crate::formula::FALSE || symbol == crate::formula::BINDER
}

/// The value of a ground term, or `None` if it contains a variable, an
/// uninterpreted symbol, or an intermediate value outside `i128`.
pub(crate) fn eval_term(term: &Term) -> Option<i128> {
    match term {
        Term::Var(_) => None,
        Term::Fun(symbol, args) => match (symbol.as_str(), args.as_slice()) {
            (numeral, []) if is_numeral(numeral) => numeral.parse().ok(),
            ("neg", [a]) => eval_term(a)?.checked_neg(),
            ("+", [a, b]) => eval_term(a)?.checked_add(eval_term(b)?),
            ("-", [a, b]) => eval_term(a)?.checked_sub(eval_term(b)?),
            ("*", [a, b]) => eval_term(a)?.checked_mul(eval_term(b)?),
            _ => None,
        },
    }
}

/// The truth value of a ground atomic proposition, or `None` if the atom is
/// not ground. The atom `false` is always false.
pub(crate) fn eval_atom(prop: &Prop) -> Option<bool> {
    match prop {
        Prop::Atom(name) if name == crate::formula::FALSE => Some(false),
        Prop::Eq(a, b) => Some(eval_term(a)? == eval_term(b)?),
        Prop::Pred(symbol, args) => match (symbol.as_str(), args.as_slice()) {
            ("<=", [a, b]) => Some(eval_term(a)? <= eval_term(b)?),
            ("<", [a, b]) => Some(eval_term(a)? < eval_term(b)?),
            _ => None,
        },
        _ => None,
    }
}
