//! Finding Farkas certificates by linear programming.
//!
//! The kernel's Farkas rule accepts non-negative integer coefficients whose
//! combination of linear constraints has no variables and a positive constant.
//! Finding such coefficients is a feasibility problem: non-negative `c` with
//! `sum_i c_i * a_i(v) = 0` for every variable `v`, and `sum_i c_i * k_i = 1` for
//! the constants. This module solves it exactly, with rationals and the simplex
//! method, so a certificate of any size is found when one exists.
//!
//! This is untrusted. The kernel checks every certificate built from the result,
//! so a wrong answer here is rejected, never accepted.
//!
//! The linear forms follow the kernel's rules (`tpt_proof_kernel::Kernel`), and
//! they must agree with them for the certificate to check.

use std::collections::BTreeMap;

use tpt_proof_kernel::terms::{Prop, Term};

/// A linear form: a coefficient per variable, and a constant.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Form {
    /// The coefficient of each variable. Opaque terms are variables too.
    pub coefficients: BTreeMap<String, i128>,
    /// The constant.
    pub constant: i128,
}

impl Form {
    fn constant(value: i128) -> Form {
        Form {
            coefficients: BTreeMap::new(),
            constant: value,
        }
    }

    fn variable(name: &str) -> Form {
        Form {
            coefficients: BTreeMap::from([(name.to_string(), 1)]),
            constant: 0,
        }
    }

    fn is_constant(&self) -> bool {
        self.coefficients.values().all(|c| *c == 0)
    }

    fn scale(&self, factor: i128) -> Option<Form> {
        let mut out = Form::constant(self.constant.checked_mul(factor)?);
        for (name, c) in &self.coefficients {
            out.coefficients
                .insert(name.clone(), c.checked_mul(factor)?);
        }
        Some(out)
    }

    fn add(&self, other: &Form, sign: i128) -> Option<Form> {
        let scaled = other.scale(sign)?;
        let mut out = Form::constant(self.constant.checked_add(scaled.constant)?);
        for (name, c) in self.coefficients.iter().chain(scaled.coefficients.iter()) {
            let entry = out.coefficients.entry(name.clone()).or_insert(0);
            *entry = entry.checked_add(*c)?;
        }
        Some(out)
    }
}

/// The linear form of an integer term, as the kernel reads it.
pub fn linear(term: &Term) -> Option<Form> {
    match term {
        Term::Var(_) => None,
        Term::Ite(..) => Some(Form::variable(&format!("{term:?}"))),
        Term::Fun(symbol, args) => match (symbol.as_str(), args.as_slice()) {
            (numeral, []) if is_numeral(numeral) => Some(Form::constant(numeral.parse().ok()?)),
            (name, []) => Some(Form::variable(name)),
            ("neg", [a]) => linear(a)?.scale(-1),
            ("+", [a, b]) => linear(a)?.add(&linear(b)?, 1),
            ("-", [a, b]) => linear(a)?.add(&linear(b)?, -1),
            ("*", [a, b]) => match (linear(a), linear(b)) {
                (Some(left), Some(right)) if left.is_constant() => right.scale(left.constant),
                (Some(left), Some(right)) if right.is_constant() => left.scale(right.constant),
                _ => Some(Form::variable(&format!("{term:?}"))),
            },
            _ => Some(Form::variable(&format!("{term:?}"))),
        },
    }
}

/// Whether a symbol is a numeral in canonical decimal form.
fn is_numeral(symbol: &str) -> bool {
    !symbol.is_empty()
        && symbol.bytes().all(|b| b.is_ascii_digit())
        && (symbol == "0" || !symbol.starts_with('0'))
}

/// The constraint `f <= 0` that a premise states, as the kernel reads it: `t <= s`
/// is `t - s <= 0`, `t < s` is `t - s + 1 <= 0`, `not (t <= s)` is `s - t + 1 <= 0`,
/// and `not (t < s)` is `s - t <= 0`.
pub fn premise_form(premise: &Prop) -> Option<Form> {
    match premise {
        Prop::Pred(symbol, args) if symbol == "<=" => match args.as_slice() {
            [t, s] => linear(t)?.add(&linear(s)?, -1),
            _ => None,
        },
        Prop::Pred(symbol, args) if symbol == "<" => match args.as_slice() {
            [t, s] => linear(t)?.add(&linear(s)?, -1)?.add(&Form::constant(1), 1),
            _ => None,
        },
        Prop::Imp(atom, bottom) if matches!(&**bottom, Prop::Atom(name) if name == "false") => {
            match &**atom {
                Prop::Pred(symbol, args) if symbol == "<=" => match args.as_slice() {
                    [t, s] => linear(s)?.add(&linear(t)?, -1)?.add(&Form::constant(1), 1),
                    _ => None,
                },
                Prop::Pred(symbol, args) if symbol == "<" => match args.as_slice() {
                    [t, s] => linear(s)?.add(&linear(t)?, -1),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// Non-negative integer coefficients for the premises whose combination is a
/// positive constant with no variables, or `None` if there are none (or the
/// arithmetic overflows).
pub fn certificate(forms: &[Form]) -> Option<Vec<i128>> {
    let mut variables: Vec<String> = forms
        .iter()
        .flat_map(|form| form.coefficients.keys().cloned())
        .collect();
    variables.sort();
    variables.dedup();
    // One equation per variable, and one for the constant (which must be 1).
    let mut rows: Vec<(Vec<Rational>, Rational)> = Vec::new();
    for variable in &variables {
        let row = forms
            .iter()
            .map(|form| Rational::from(*form.coefficients.get(variable).unwrap_or(&0)))
            .collect();
        rows.push((row, Rational::from(0)));
    }
    rows.push((
        forms
            .iter()
            .map(|form| Rational::from(form.constant))
            .collect(),
        Rational::from(1),
    ));
    let solution = solve_nonnegative(&rows, forms.len())?;
    // Scale to integers. The constant of the combination stays positive.
    let mut scale: i128 = 1;
    for value in &solution {
        scale = lcm(scale, value.den)?;
    }
    solution
        .iter()
        .map(|value| value.num.checked_mul(scale / value.den))
        .collect()
}

/// A rational number in lowest terms, with a positive denominator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Rational {
    num: i128,
    den: i128,
}

impl From<i128> for Rational {
    fn from(num: i128) -> Rational {
        Rational { num, den: 1 }
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn lcm(a: i128, b: i128) -> Option<i128> {
    (a / gcd(a, b)).checked_mul(b)
}

impl Rational {
    fn new(num: i128, den: i128) -> Option<Rational> {
        if den == 0 {
            return None;
        }
        let g = gcd(num, den).max(1);
        let sign = if den < 0 { -1 } else { 1 };
        Some(Rational {
            num: sign * num / g,
            den: sign * den / g,
        })
    }

    fn is_zero(self) -> bool {
        self.num == 0
    }

    fn add(self, other: Rational) -> Option<Rational> {
        let num = self
            .num
            .checked_mul(other.den)?
            .checked_add(other.num.checked_mul(self.den)?)?;
        Rational::new(num, self.den.checked_mul(other.den)?)
    }

    fn sub(self, other: Rational) -> Option<Rational> {
        self.add(Rational {
            num: -other.num,
            den: other.den,
        })
    }

    fn mul(self, other: Rational) -> Option<Rational> {
        Rational::new(
            self.num.checked_mul(other.num)?,
            self.den.checked_mul(other.den)?,
        )
    }

    fn div(self, other: Rational) -> Option<Rational> {
        if other.is_zero() {
            return None;
        }
        Rational::new(
            self.num.checked_mul(other.den)?,
            self.den.checked_mul(other.num)?,
        )
    }

    fn less(self, other: Rational) -> Option<bool> {
        Some(self.num.checked_mul(other.den)? < other.num.checked_mul(self.den)?)
    }
}

/// The values of the `n` original variables in a feasible point of
/// `A x = b`, `x >= 0`, found by phase-one simplex with Bland's rule. `None` when
/// the system has no non-negative solution.
fn solve_nonnegative(rows: &[(Vec<Rational>, Rational)], n: usize) -> Option<Vec<Rational>> {
    let m = rows.len();
    // Tableau: m constraint rows, then the objective row. Columns: n original
    // variables, m artificials, then the right-hand side.
    let width = n + m + 1;
    let rhs = width - 1;
    let mut tableau: Vec<Vec<Rational>> = Vec::with_capacity(m + 1);
    for (i, (coefficients, target)) in rows.iter().enumerate() {
        // Make the right-hand side non-negative by negating the row if needed.
        let flip = target.less(Rational::from(0)).unwrap_or(false);
        let sign = if flip { -1 } else { 1 };
        let mut row = vec![Rational::from(0); width];
        for (j, value) in coefficients.iter().enumerate() {
            row[j] = Rational::from(sign).mul(*value)?;
        }
        row[n + i] = Rational::from(1);
        row[rhs] = Rational::from(sign).mul(*target)?;
        tableau.push(row);
    }
    // The phase-one objective: minimise the sum of the artificials. Its reduced
    // costs are the negated column sums of the constraint rows, zero for the
    // artificials.
    let mut objective = vec![Rational::from(0); width];
    for row in &tableau {
        for (j, value) in row.iter().enumerate().take(n) {
            objective[j] = objective[j].sub(*value)?;
        }
        objective[rhs] = objective[rhs].sub(row[rhs])?;
    }
    tableau.push(objective);
    let mut basis: Vec<usize> = (0..m).map(|i| n + i).collect();

    // Bland's rule: the smallest entering column with a negative reduced cost, and
    // among the tied rows, the one whose basic variable has the smallest index.
    loop {
        let entering = (0..n + m).find(|&j| tableau[m][j].less(Rational::from(0)).unwrap_or(false));
        let Some(entering) = entering else {
            break;
        };
        let mut leaving: Option<(usize, Rational)> = None;
        for i in 0..m {
            let pivot = tableau[i][entering];
            if !Rational::from(0).less(pivot).unwrap_or(false) {
                continue;
            }
            let ratio = tableau[i][rhs].div(pivot)?;
            let better = match leaving {
                None => true,
                Some((best, best_ratio)) => {
                    ratio.less(best_ratio).unwrap_or(false)
                        || (ratio == best_ratio && basis[i] < basis[best])
                }
            };
            if better {
                leaving = Some((i, ratio));
            }
        }
        let (row, _) = leaving?;
        pivot(&mut tableau, row, entering)?;
        basis[row] = entering;
    }
    // The phase-one objective holds the negated sum of the artificials. Zero means
    // every artificial left the basis, so the system is feasible.
    if !tableau[m][rhs].is_zero() {
        return None;
    }
    let mut values = vec![Rational::from(0); n];
    for (i, &variable) in basis.iter().enumerate() {
        if variable < n {
            values[variable] = tableau[i][rhs];
        }
    }
    Some(values)
}

/// Pivots the tableau on `(row, column)`.
fn pivot(tableau: &mut [Vec<Rational>], row: usize, column: usize) -> Option<()> {
    let width = tableau[row].len();
    let divisor = tableau[row][column];
    for value in tableau[row].iter_mut() {
        *value = value.div(divisor)?;
    }
    let pivot_row = tableau[row].clone();
    for (i, other) in tableau.iter_mut().enumerate() {
        if i == row || other[column].is_zero() {
            continue;
        }
        let factor = other[column];
        for j in 0..width {
            other[j] = other[j].sub(factor.mul(pivot_row[j])?)?;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn form(coefficients: &[(&str, i128)], constant: i128) -> Form {
        Form {
            coefficients: coefficients
                .iter()
                .map(|(name, c)| (name.to_string(), *c))
                .collect(),
            constant,
        }
    }

    #[test]
    fn a_two_coefficient_certificate_is_found() {
        // x <= 0 and -x + 1 <= 0 (that is 1 <= x): the sum 1 <= 0 is false.
        let forms = [form(&[("x", 1)], 0), form(&[("x", -1)], 1)];
        let coefficients = certificate(&forms).expect("a certificate");
        assert_eq!(coefficients, vec![1, 1]);
    }

    #[test]
    fn a_certificate_needs_coefficient_two_and_is_found() {
        // 2x - 255 <= 0, and x - 127 + ... : 2 * (x - 128 + 1) + (255 - 2x + 1)... use
        // the rounding example: x >= 128 (as 128 - x <= 0) and 2x - 255 <= 0.
        let forms = [form(&[("x", -1)], 128), form(&[("x", 2)], -255)];
        let coefficients = certificate(&forms).expect("a certificate");
        // 2 * (128 - x) + (2x - 255) = 1.
        assert_eq!(coefficients, vec![2, 1]);
    }

    #[test]
    fn a_consistent_system_has_no_certificate() {
        // x <= 0 and -x <= 0 are consistent (x = 0).
        let forms = [form(&[("x", 1)], 0), form(&[("x", -1)], 0)];
        assert!(certificate(&forms).is_none());
    }

    #[test]
    fn a_long_chain_is_found_without_enumerating_coefficients() {
        // x_i + 1 <= x_{i+1} for i < 9, and x_9 <= x_0. Summing the chain gives
        // 9 <= 0. Ten premises would be 3^10 choices to enumerate; the simplex finds
        // the all-ones certificate directly.
        let names: Vec<String> = (0..10).map(|i| format!("x{i}")).collect();
        let mut forms = Vec::new();
        for i in 0..9 {
            forms.push(form(
                &[(names[i].as_str(), 1), (names[i + 1].as_str(), -1)],
                1,
            ));
        }
        forms.push(form(&[(names[9].as_str(), 1), (names[0].as_str(), -1)], 0));
        let coefficients = certificate(&forms).expect("a certificate");
        assert_eq!(coefficients, vec![1; 10]);
    }
}
