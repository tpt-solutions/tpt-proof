//! The Farkas rule ([`crate::ProofTerm::Farkas`]): linear integer contradictions.
//!
//! A premise is one of two linear constraints over `Int`:
//!
//! - `t <= s` is the constraint `t - s <= 0`;
//! - `not (t <= s)`, written as the implication `t <= s -> false`, is the
//!   constraint `s - t + 1 <= 0`, because over the integers `t > s` is `s + 1 <= t`.
//!
//! Given non-negative coefficients `c_i`, the rule checks that the combination
//! `sum c_i * f_i` has no variables and a constant greater than zero. Every
//! `f_i` is at most zero, so the combination is at most zero and also equals a
//! positive constant: the premises are contradictory. The rule then proves
//! `P_1 -> ... -> P_k -> false`.
//!
//! This is trusted, and it is small: the linear form of a term, the sign of
//! each coefficient, and the two constraint shapes above. Integer arithmetic
//! is checked in `i128`, and an overflow is refused rather than wrapped.

use crate::formula::FALSE;
use crate::linear::{constraint, Linear};
use crate::terms::Prop;
use crate::{Kernel, KernelError, Result};

/// Checks a Farkas certificate. On success the result is the proposition
/// `P_1 -> ... -> P_k -> false`, which the premises refute.
pub(crate) fn check(kernel: &Kernel, premises: &[Prop], coefficients: &[i128]) -> Result<Prop> {
    let reject = |reason: &str| KernelError::FarkasRejected(reason.to_string());
    if premises.len() != coefficients.len() {
        return Err(reject("the certificate needs one coefficient per premise"));
    }
    if premises.is_empty() {
        return Err(reject("the certificate has no premises"));
    }
    let mut total = Linear::default();
    for (premise, coefficient) in premises.iter().zip(coefficients) {
        if *coefficient < 0 {
            return Err(reject("a coefficient is negative"));
        }
        kernel.check_prop(premise, &[])?;
        let form = constraint(premise)
            .ok_or_else(|| reject("a premise is not a linear integer constraint"))?;
        let scaled = form
            .scale(*coefficient)
            .ok_or_else(|| reject("the combination overflows"))?;
        total = total
            .add(&scaled, 1)
            .ok_or_else(|| reject("the combination overflows"))?;
    }
    if !total.is_constant() {
        return Err(reject("the combination still mentions a variable"));
    }
    if total.constant <= 0 {
        return Err(reject("the combination is not a positive constant"));
    }
    Ok(premises
        .iter()
        .rev()
        .fold(Prop::atom(FALSE), |acc, premise| {
            Prop::imp(premise.clone(), acc)
        }))
}
