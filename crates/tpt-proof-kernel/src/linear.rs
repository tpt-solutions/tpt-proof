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
/// The linear form of an integer term. A term that is not linear, such as a
/// product of two variables, a `div` or `mod`, or an array read, is an opaque
/// unknown integer: the form treats it as a variable named by the term. Equal
/// opaque terms are the same variable, and no other fact is assumed, so every
/// identity or contradiction found this way holds for every integer value of
/// the opaque terms. `None` only when a coefficient overflows.
pub(crate) fn linear(term: &Term) -> Option<Linear> {
    let opaque = || Some(Linear::variable(&format!("{term:?}")));
    match term {
        Term::Var(_) => None,
        Term::Fun(symbol, args) => match (symbol.as_str(), args.as_slice()) {
            (numeral, []) if is_numeral(numeral) => Some(Linear::constant(numeral.parse().ok()?)),
            (name, []) => Some(Linear::variable(name)),
            ("neg", [a]) => linear(a)?.scale(-1),
            ("+", [a, b]) => linear(a)?.add(&linear(b)?, 1),
            ("-", [a, b]) => linear(a)?.add(&linear(b)?, -1),
            ("*", [a, b]) => match (linear(a), linear(b)) {
                (Some(left), Some(right)) if left.is_constant() => right.scale(left.constant),
                (Some(left), Some(right)) if right.is_constant() => left.scale(right.constant),
                _ => opaque(),
            },
            _ => opaque(),
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
    // The difference `t - s` of each side, with the relation it must satisfy.
    let difference = |prop: &Prop| match prop {
        Prop::Pred(symbol, args) if symbol == "<=" => match args.as_slice() {
            [t, s] => linear(t)?.add(&linear(s)?, -1).map(|form| (form, false)),
            _ => None,
        },
        Prop::Eq(t, s) => linear(t)?.add(&linear(s)?, -1).map(|form| (form, true)),
        _ => None,
    };
    let (Some((f, f_is_eq)), Some((g, g_is_eq))) = (difference(a), difference(b)) else {
        return Err(reject(
            "both sides must be `t <= s` constraints or equations over linear integer terms",
        ));
    };
    if f_is_eq != g_is_eq {
        return Err(reject("an inequality cannot stand for an equation"));
    }
    // `f <= 0` depends only on `f`. `f = 0` is the same as `-f = 0`, so an
    // equation may match with either sign.
    let same = if f_is_eq {
        f == g || g.scale(-1).is_some_and(|negated| f == negated)
    } else {
        f == g
    };
    if !same {
        return Err(reject("the two sides have different linear forms"));
    }
    Ok(Prop::imp(a.clone(), b.clone()))
}

/// Checks the linear identity rule: `t = s` for two integer terms with the same
/// linear form. Each term denotes the same integer under every valuation of its
/// variables, so the equation holds.
pub(crate) fn check_identity(kernel: &crate::Kernel, t: &Term, s: &Term) -> crate::Result<Prop> {
    let prop = Prop::Eq(t.clone(), s.clone());
    kernel.check_prop(&prop, &[])?;
    match (linear(t), linear(s)) {
        (Some(left), Some(right)) if left == right => Ok(prop),
        _ => Err(crate::KernelError::LinearRejected(
            "the two terms have different linear forms".to_string(),
        )),
    }
}
