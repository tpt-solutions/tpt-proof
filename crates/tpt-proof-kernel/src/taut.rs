//! The tautology rule ([`crate::ProofTerm::Taut`]).
//!
//! A formula is accepted when it is true under every valuation of its letters.
//! A letter is an atom that is not ground; ground atoms are evaluated with the
//! built-in arithmetic (see [`crate::arith`]). Checking is a truth table, so
//! the rule refuses formulas with more than [`MAX_LETTERS`] letters.
//!
//! This rule is part of the trusted base. It makes the kernel classical: the
//! truth table decides the formula, so for example `not not a -> a` is
//! accepted with no excluded-middle axiom. The encodings in
//! [`crate::formula`] must be classically correct for this to be sound.

use crate::arith::eval_atom;
use crate::formula::Formula;
use crate::terms::alpha_eq;
use crate::{Kernel, KernelError, Result};

/// The most letters a tautology may have. The truth table has `2^n` rows.
pub const MAX_LETTERS: usize = 16;

/// Checks that `formula` is a tautology, after checking its atoms.
pub(crate) fn check(kernel: &Kernel, formula: &Formula) -> Result<()> {
    let mut atoms = Vec::new();
    formula.atoms(&mut atoms);
    for atom in &atoms {
        kernel.check_prop(atom, &[])?;
    }

    let mut letters: Vec<&crate::terms::Prop> = Vec::new();
    for atom in atoms {
        if eval_atom(atom).is_none() && !letters.iter().any(|letter| alpha_eq(letter, atom)) {
            letters.push(atom);
        }
    }
    if letters.len() > MAX_LETTERS {
        return Err(KernelError::TooManyLetters(letters.len()));
    }

    for valuation in 0..(1usize << letters.len()) {
        if !holds(formula, &letters, valuation) {
            return Err(KernelError::NotATautology(formula.encode()));
        }
    }
    Ok(())
}

/// Whether `formula` is true when letter `i` has the truth value of bit `i`
/// of `valuation`.
fn holds(formula: &Formula, letters: &[&crate::terms::Prop], valuation: usize) -> bool {
    match formula {
        Formula::Atom(prop) => match eval_atom(prop) {
            Some(value) => value,
            // Every non-ground atom was collected as a letter, so the position
            // is always found. Failing closed keeps the rule sound regardless.
            None => letters
                .iter()
                .position(|letter| alpha_eq(letter, prop))
                .is_some_and(|index| valuation >> index & 1 == 1),
        },
        Formula::Const(value) => *value,
        Formula::Not(a) => !holds(a, letters, valuation),
        Formula::And(items) => items.iter().all(|item| holds(item, letters, valuation)),
        Formula::Or(items) => items.iter().any(|item| holds(item, letters, valuation)),
        Formula::Imp(a, b) => !holds(a, letters, valuation) || holds(b, letters, valuation),
        Formula::Iff(a, b) => holds(a, letters, valuation) == holds(b, letters, valuation),
    }
}
