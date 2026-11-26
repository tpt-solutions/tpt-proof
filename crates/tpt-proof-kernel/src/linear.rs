//! Linear integer forms, shared by the Farkas rule ([`crate::farkas`]) and the
//! linear equivalence rule ([`crate::ProofTerm::Linear`]).
//!
//! A term is linear when it is built from integer variables, numerals, `+`,
//! `-`, `neg`, and `*` where one factor is a constant. Its linear form is a
//! coefficient per variable and a constant. Overflow is refused, never wrapped.

use std::collections::BTreeMap;

use crate::arith::is_numeral;
use crate::formula::FALSE;
use crate::terms::{Prop, Term};

/// A linear form: a coefficient per variable, and a constant.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Linear {
    pub(crate) coefficients: BTreeMap<String, i128>,
    pub(crate) constant: i128,
}

impl Linear {
    pub(crate) fn constant(value: i128) -> Linear {
        Linear {
            coefficients: BTreeMap::new(),
            constant: value,
        }
    }

    pub(crate) fn variable(name: &str) -> Linear {
        Linear {
            coefficients: BTreeMap::from([(name.to_string(), 1)]),
            constant: 0,
        }
    }

    pub(crate) fn is_constant(&self) -> bool {
        self.coefficients.values().all(|c| *c == 0)
    }

    pub(crate) fn scale(&self, factor: i128) -> Option<Linear> {
        let mut out = Linear::constant(self.constant.checked_mul(factor)?);
        for (name, c) in &self.coefficients {
            out.coefficients
                .insert(name.clone(), c.checked_mul(factor)?);
        }
        Some(out)
    }

    pub(crate) fn add(&self, other: &Linear, sign: i128) -> Option<Linear> {
        let scaled = other.scale(sign)?;
        let mut out = Linear::constant(self.constant.checked_add(scaled.constant)?);
        for (name, c) in self.coefficients.iter().chain(scaled.coefficients.iter()) {
            let entry = out.coefficients.entry(name.clone()).or_insert(0);
            *entry = entry.checked_add(*c)?;
        }
        Some(out)
    }
}

/// The linear form of an integer term, or `None` if it is not linear.
pub(crate) fn linear(term: &Term) -> Option<Linear> {
    match term {
        Term::Var(_) => None,
        Term::Fun(symbol, args) => match (symbol.as_str(), args.as_slice()) {
            (numeral, []) if is_numeral(numeral) => Some(Linear::constant(numeral.parse().ok()?)),
            (name, []) => Some(Linear::variable(name)),
            ("neg", [a]) => linear(a)?.scale(-1),
            ("+", [a, b]) => linear(a)?.add(&linear(b)?, 1),
            ("-", [a, b]) => linear(a)?.add(&linear(b)?, -1),
            ("*", [a, b]) => {
                let (left, right) = (linear(a)?, linear(b)?);
                if left.is_constant() {
                    right.scale(left.constant)
                } else if right.is_constant() {
                    left.scale(right.constant)
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

/// The constraint `f <= 0` that a premise states, or `None` if it has another shape.
pub(crate) fn constraint(premise: &Prop) -> Option<Linear> {
    match premise {
        Prop::Pred(symbol, args) if symbol == "<=" => match args.as_slice() {
            [t, s] => linear(t)?.add(&linear(s)?, -1),
            _ => None,
        },
        Prop::Imp(atom, bottom) if matches!(&**bottom, Prop::Atom(name) if name == FALSE) => {
            match &**atom {
                // not (t <= s) is s + 1 <= t, that is s - t + 1 <= 0.
                Prop::Pred(symbol, args) if symbol == "<=" => match args.as_slice() {
                    [t, s] => linear(s)?
                        .add(&linear(t)?, -1)?
                        .add(&Linear::constant(1), 1),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// Checks the linear equivalence rule: `a -> b` for two constraints `t <= s`
/// whose differences `t - s` have the same linear form. Over the integers the
/// constraint `f <= 0` depends only on the form `f`, so the two constraints
/// are equivalent and the implication holds in both directions.
pub(crate) fn check_implication(kernel: &crate::Kernel, a: &Prop, b: &Prop) -> crate::Result<Prop> {
    let reject = |reason: &str| crate::KernelError::LinearRejected(reason.to_string());
    kernel.check_prop(a, &[])?;
    kernel.check_prop(b, &[])?;
    let (Prop::Pred(left, left_args), Prop::Pred(right, right_args)) = (a, b) else {
        return Err(reject("both sides must be `t <= s` constraints"));
    };
    if left != "<=" || right != "<=" {
        return Err(reject("both sides must be `t <= s` constraints"));
    }
    let difference = |args: &[Term]| match args {
        [t, s] => linear(t)?.add(&linear(s)?, -1),
        _ => None,
    };
    let (Some(f), Some(g)) = (difference(left_args), difference(right_args)) else {
        return Err(reject("a side is not a linear integer constraint"));
    };
    if f != g {
        return Err(reject("the two sides have different linear forms"));
    }
    Ok(Prop::imp(a.clone(), b.clone()))
}
