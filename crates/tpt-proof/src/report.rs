//! Dependency reports: which axioms each checked theorem relies on.
//!
//! The report only reads the kernel. It lists every theorem with its statement
//! and the axioms it depends on, with each axiom's justification, so a reviewer
//! can see what a result rests on.

use std::fmt;

use tpt_proof_kernel::Kernel;

/// A report over a kernel's theorems. Build it with [`dependency_report`].
pub struct DependencyReport<'k> {
    kernel: &'k Kernel,
}

/// The dependency report for every theorem in `kernel`.
pub fn dependency_report(kernel: &Kernel) -> DependencyReport<'_> {
    DependencyReport { kernel }
}

impl fmt::Display for DependencyReport<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut theorems = 0;
        for (name, theorem) in self.kernel.theorems() {
            theorems += 1;
            writeln!(f, "theorem {name}: {}", theorem.prop())?;
            if theorem.axioms().is_empty() {
                writeln!(f, "  depends on no axioms")?;
            }
            for axiom in theorem.axioms() {
                match self.kernel.axiom(axiom) {
                    Some(decl) => {
                        writeln!(f, "  axiom {axiom}: {} ({})", decl.prop, decl.justification)?
                    }
                    None => writeln!(f, "  axiom {axiom}: not declared")?,
                }
            }
        }
        writeln!(f, "{theorems} theorem(s)")
    }
}

#[cfg(test)]
mod tests {
    use tpt_proof_kernel::terms::Prop;

    use super::*;

    #[test]
    fn report_lists_each_theorem_with_its_axioms_and_justifications() {
        let mut kernel = Kernel::new();
        kernel
            .declare_axiom("ax_a", Prop::atom("A"), "a test axiom")
            .expect("declares");
        let term = tpt_proof_kernel::ProofTerm::Axiom("ax_a".to_string());
        kernel
            .declare_theorem("uses_a", &term, &Prop::atom("A"))
            .expect("checks");
        kernel
            .declare_theorem(
                "pure",
                &tpt_proof_kernel::ProofTerm::Lam(
                    "h".to_string(),
                    Prop::atom("B"),
                    Box::new(tpt_proof_kernel::ProofTerm::Var("h".to_string())),
                ),
                &Prop::imp(Prop::atom("B"), Prop::atom("B")),
            )
            .expect("checks");

        let text = dependency_report(&kernel).to_string();
        assert!(text.contains("theorem uses_a: A"), "{text}");
        assert!(text.contains("axiom ax_a: A (a test axiom)"), "{text}");
        assert!(text.contains("theorem pure: (B -> B)"), "{text}");
        assert!(text.contains("depends on no axioms"), "{text}");
        assert!(text.ends_with("2 theorem(s)\n"), "{text}");
    }
}
