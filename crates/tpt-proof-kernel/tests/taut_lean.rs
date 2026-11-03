//! Cross-check of the tautology rule with Lean 4.
//!
//! For generated formulas, the kernel's verdict is compared with Lean's: Lean
//! must prove every formula the kernel accepts, and must reject every formula
//! the kernel refuses. Lean reads the formula with its own connectives (`¬`,
//! `∧`, `∨`, `→`, `↔`), so this checks the truth table in `taut.rs`, not the
//! encodings in `formula.rs`. The encodings are checked by review and by the
//! property test in `taut_property.rs`.
//!
//! Needs `lean` on the PATH. Run with `cargo test -- --ignored`.

#[path = "../../../tests-support/tools.rs"]
mod tools;

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::terms::{ProofTerm, Prop};
use tpt_proof_kernel::Kernel;

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
    match rng.below(6) {
        0 => Formula::Not(Box::new(gen(rng, depth - 1))),
        1 => Formula::Imp(Box::new(gen(rng, depth - 1)), Box::new(gen(rng, depth - 1))),
        2 => Formula::Iff(Box::new(gen(rng, depth - 1)), Box::new(gen(rng, depth - 1))),
        3 => Formula::And(vec![gen(rng, depth - 1), gen(rng, depth - 1)]),
        4 => Formula::Or(vec![gen(rng, depth - 1), gen(rng, depth - 1)]),
        _ => Formula::Or(vec![
            gen(rng, depth - 1),
            gen(rng, depth - 1),
            gen(rng, depth - 1),
        ]),
    }
}

/// Renders the formula with Lean's connectives. Letters are Lean propositions.
fn lean_text(formula: &Formula) -> String {
    let join = |items: &[Formula], op: &str, empty: &str| -> String {
        if items.is_empty() {
            return empty.to_string();
        }
        let parts: Vec<String> = items.iter().map(lean_text).collect();
        format!("({})", parts.join(&format!(" {op} ")))
    };
    match formula {
        Formula::Atom(Prop::Atom(name)) => name.clone(),
        Formula::Atom(_) => unreachable!("the generator only makes letters"),
        Formula::Const(true) => "True".to_string(),
        Formula::Const(false) => "False".to_string(),
        Formula::Not(a) => format!("¬{}", lean_text(a)),
        Formula::And(items) => join(items, "∧", "True"),
        Formula::Or(items) => join(items, "∨", "False"),
        Formula::Imp(a, b) => format!("({} → {})", lean_text(a), lean_text(b)),
        Formula::Iff(a, b) => format!("({} ↔ {})", lean_text(a), lean_text(b)),
    }
}

/// A Lean file that states the formula and proves it by splitting on each letter.
fn lean_file(formula: &Formula) -> String {
    let mut text = String::from("variable (A B C : Prop)\n\n");
    let _ = writeln!(
        text,
        "theorem check (A B C : Prop) : {} := by",
        lean_text(formula)
    );
    text.push_str("  classical\n");
    text.push_str("  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp_all\n");
    text
}

/// Whether Lean accepts the file. Each case gets its own file, so cases can run
/// in any order without clashing.
fn lean_accepts(index: usize, formula: &Formula) -> bool {
    let path: PathBuf = std::env::temp_dir().join(format!("tpt_taut_{index}.lean"));
    std::fs::write(&path, lean_file(formula)).expect("write the Lean file");
    let output = Command::new("lean")
        .arg(&path)
        .output()
        .expect("run lean (it must be on the PATH)");
    let _ = std::fs::remove_file(&path);
    output.status.success()
}

#[test]
fn lean_agrees_with_the_kernel_on_generated_formulas() {
    if tools::skip_unless("lean") {
        return;
    }
    let kernel = Kernel::new();
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let mut accepted = 0;
    let mut refused = 0;
    for index in 0..150 {
        let depth = 1 + rng.below(3);
        let formula = gen(&mut rng, depth);
        let kernel_accepts = kernel
            .check_proof(&ProofTerm::Taut(formula.clone()), &formula.encode())
            .is_ok();
        let lean_proves = lean_accepts(index, &formula);
        assert_eq!(
            kernel_accepts,
            lean_proves,
            "kernel and Lean disagree on {formula:?}\n{}",
            lean_file(&formula)
        );
        if kernel_accepts {
            accepted += 1;
        } else {
            refused += 1;
        }
    }
    // Both verdicts must occur, or the comparison checks nothing.
    assert!(accepted > 10, "only {accepted} tautologies");
    assert!(refused > 10, "only {refused} non-tautologies");
}
