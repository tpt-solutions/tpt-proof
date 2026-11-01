//! Property-based tests with a deterministic generator.
//!
//! The crate has zero dependencies, so there is no proptest here. A small
//! xorshift generator with fixed seeds keeps every run reproducible. The
//! properties check soundness-relevant invariants, not just examples.

use tpt_proof_kernel::{Kernel, ProofTerm, Prop};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64: fixed-seed, reproducible, good enough for test generation.
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

const ATOMS: [&str; 3] = ["A", "B", "C"];
const BOUND: [&str; 2] = ["p", "q"];

fn gen_prop(rng: &mut Rng, depth: usize) -> Prop {
    if depth == 0 || rng.below(3) == 0 {
        return Prop::atom(ATOMS[rng.below(3)]);
    }
    match rng.below(3) {
        0 => Prop::imp(gen_prop(rng, depth - 1), gen_prop(rng, depth - 1)),
        1 => Prop::forall(BOUND[rng.below(2)], gen_prop(rng, depth - 1)),
        _ => Prop::atom(ATOMS[rng.below(3)]),
    }
}

/// Builds a random term. `scope` holds the names bound by enclosing binders,
/// so the term is closed.
fn gen_term(rng: &mut Rng, depth: usize, scope: &mut Vec<String>) -> ProofTerm {
    if depth == 0 {
        return match scope.last() {
            Some(name) if rng.below(2) == 0 => ProofTerm::Var(name.clone()),
            _ => ProofTerm::Axiom("missing".to_string()),
        };
    }
    match rng.below(5) {
        0 => match scope.last() {
            Some(name) => ProofTerm::Var(name.clone()),
            None => ProofTerm::Axiom("missing".to_string()),
        },
        1 => {
            let name = format!("x{}", scope.len());
            let domain = gen_prop(rng, 2);
            scope.push(name.clone());
            let body = gen_term(rng, depth - 1, scope);
            scope.pop();
            ProofTerm::Lam(name, domain, Box::new(body))
        }
        2 => ProofTerm::App(
            Box::new(gen_term(rng, depth - 1, scope)),
            Box::new(gen_term(rng, depth - 1, scope)),
        ),
        3 => ProofTerm::TyLam(
            BOUND[rng.below(2)].to_string(),
            Box::new(gen_term(rng, depth - 1, scope)),
        ),
        _ => ProofTerm::TyApp(Box::new(gen_term(rng, depth - 1, scope)), gen_prop(rng, 2)),
    }
}

#[test]
fn checker_never_panics_on_random_terms() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let kernel = Kernel::new();
    for _ in 0..2_000 {
        let term = gen_term(&mut rng, 5, &mut Vec::new());
        let claimed = gen_prop(&mut rng, 3);
        // Either outcome is fine; the property is that nothing panics.
        let _ = kernel.check_proof(&term, &claimed);
    }
}

#[test]
fn closed_terms_never_prove_an_atom_without_axioms() {
    // With no axioms and no assumptions, no closed term has an atomic type.
    // This is the basic soundness check: proofs cannot come from nothing.
    let mut rng = Rng(0x0123_4567_89AB_CDEF);
    let kernel = Kernel::new();
    let mut accepted = 0;
    for _ in 0..2_000 {
        let term = gen_term(&mut rng, 5, &mut Vec::new());
        for atom in ATOMS {
            if kernel.check_proof(&term, &Prop::atom(atom)).is_ok() {
                accepted += 1;
            }
        }
    }
    assert_eq!(accepted, 0, "a closed term proved an atom with no axioms");
}

#[test]
fn accepted_proofs_depend_only_on_declared_axioms() {
    let mut rng = Rng(0xDEAD_BEEF_CAFE_F00D);
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", Prop::atom("A"), "test axiom")
        .expect("declare");
    kernel
        .declare_axiom(
            "ax_ab",
            Prop::imp(Prop::atom("A"), Prop::atom("B")),
            "test axiom",
        )
        .expect("declare");

    for _ in 0..2_000 {
        let term = gen_term(&mut rng, 5, &mut Vec::new());
        let claimed = gen_prop(&mut rng, 3);
        if let Ok(thm) = kernel.check_proof(&term, &claimed) {
            assert_eq!(thm.prop(), &claimed);
            for dep in thm.axioms() {
                assert!(
                    kernel.axiom(dep).is_some(),
                    "theorem depends on undeclared `{dep}`"
                );
            }
        }
    }
}

#[test]
fn proof_search_finds_proofs_of_random_goals() {
    // A depth-first search over introduction rules and the axiom set. Any
    // proof it finds must be accepted by the kernel, which is a consistency
    // check between the search and the checker.
    let mut rng = Rng(0x5151_5151_5151_5151);
    let mut kernel = Kernel::new();
    kernel
        .declare_axiom("ax_a", Prop::atom("A"), "test axiom")
        .expect("declare");

    let mut found = 0;
    for _ in 0..500 {
        let goal = gen_prop(&mut rng, 3);
        if let Some(term) = search(&kernel, &goal, &mut Vec::new(), 4) {
            found += 1;
            assert!(kernel.check_proof(&term, &goal).is_ok());
        }
    }
    assert!(found > 0, "search found no proofs at all");
}

fn search(
    kernel: &Kernel,
    goal: &Prop,
    scope: &mut Vec<(String, Prop)>,
    fuel: usize,
) -> Option<ProofTerm> {
    if fuel == 0 {
        return None;
    }
    // Use a hypothesis or the axiom, checked by the kernel itself.
    for (name, prop) in scope.iter().rev() {
        let candidate = ProofTerm::Var(name.clone());
        if prop == goal && kernel.check_proof(&candidate, goal).is_ok() {
            return Some(candidate);
        }
    }
    let axiom = ProofTerm::Axiom("ax_a".to_string());
    if kernel.check_proof(&axiom, goal).is_ok() {
        return Some(axiom);
    }
    match goal {
        Prop::Imp(domain, codomain) => {
            let name = format!("h{}", scope.len());
            scope.push((name.clone(), (**domain).clone()));
            let body = search(kernel, codomain, scope, fuel - 1);
            scope.pop();
            body.map(|body| ProofTerm::Lam(name, (**domain).clone(), Box::new(body)))
        }
        _ => None,
    }
}
