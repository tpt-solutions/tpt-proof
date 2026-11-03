//! Property test for the tautology rule: the kernel accepts a formula exactly
//! when an independent evaluator says it holds under every valuation.
//!
//! The evaluator here shares no code with `taut.rs`. Formulas are generated
//! with a fixed-seed generator, so every run checks the same cases.

use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::terms::{ProofTerm, Prop};
use tpt_proof_kernel::{Kernel, KernelError};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64, as in property.rs.
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u64) -> usize {
        (self.next() % n) as usize
    }
}

const LETTERS: [&str; 3] = ["A", "B", "C"];

fn gen(rng: &mut Rng, depth: usize) -> Formula {
    if depth == 0 || rng.below(4) == 0 {
        return match rng.below(6) {
            0 => Formula::Const(rng.below(2) == 0),
            _ => Formula::Atom(Prop::atom(LETTERS[rng.below(3)])),
        };
    }
    match rng.below(7) {
        0 => Formula::Not(Box::new(gen(rng, depth - 1))),
        1 => Formula::Imp(Box::new(gen(rng, depth - 1)), Box::new(gen(rng, depth - 1))),
        2 => Formula::Iff(Box::new(gen(rng, depth - 1)), Box::new(gen(rng, depth - 1))),
        3 => Formula::And(vec![gen(rng, depth - 1), gen(rng, depth - 1)]),
        4 => Formula::Or(vec![gen(rng, depth - 1), gen(rng, depth - 1)]),
        5 => Formula::And(vec![gen(rng, depth - 1)]),
        _ => Formula::Or(vec![
            gen(rng, depth - 1),
            gen(rng, depth - 1),
            gen(rng, depth - 1),
        ]),
    }
}

/// The reference semantics: truth under one valuation of the three letters.
fn reference(formula: &Formula, valuation: [bool; 3]) -> bool {
    match formula {
        Formula::Atom(Prop::Atom(name)) => {
            let index = LETTERS.iter().position(|letter| letter == name).unwrap();
            valuation[index]
        }
        Formula::Atom(_) => panic!("the generator only makes letters"),
        Formula::Const(value) => *value,
        Formula::Not(a) => !reference(a, valuation),
        Formula::And(items) => items.iter().all(|item| reference(item, valuation)),
        Formula::Or(items) => items.iter().any(|item| reference(item, valuation)),
        Formula::Imp(a, b) => !reference(a, valuation) || reference(b, valuation),
        Formula::Iff(a, b) => reference(a, valuation) == reference(b, valuation),
    }
}

fn is_tautology(formula: &Formula) -> bool {
    (0..8).all(|bits| reference(formula, [bits & 1 == 1, bits & 2 == 2, bits & 4 == 4]))
}

#[test]
fn the_kernel_accepts_exactly_the_tautologies() {
    let kernel = Kernel::new();
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut accepted = 0;
    let mut rejected = 0;
    for _ in 0..2000 {
        let depth = 1 + rng.below(4);
        let formula = gen(&mut rng, depth);
        let claimed = formula.encode();
        let result = kernel.check_proof(&ProofTerm::Taut(formula.clone()), &claimed);
        let expected = is_tautology(&formula);
        match (result, expected) {
            (Ok(theorem), true) => {
                assert_eq!(theorem.prop(), &claimed);
                accepted += 1;
            }
            (Err(KernelError::NotATautology(_)), false) => rejected += 1,
            (result, expected) => {
                panic!("mismatch for {formula:?}: tautology {expected}, kernel said {result:?}")
            }
        }
    }
    // The generator must produce both outcomes, or the property checks nothing.
    assert!(accepted > 100, "only {accepted} tautologies were generated");
    assert!(
        rejected > 100,
        "only {rejected} non-tautologies were generated"
    );
}
