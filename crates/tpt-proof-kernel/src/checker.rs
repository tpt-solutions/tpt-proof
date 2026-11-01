//! The proof checker. It computes the proposition a term proves and collects the
//! axioms it uses. Checking is a plain recursive function over the term.

use std::collections::BTreeSet;

use crate::terms::{ProofTerm, Prop};
use crate::{Kernel, KernelError, Result};

/// Local proof variables in scope, innermost binding last.
pub(crate) type Context = Vec<(String, Prop)>;

/// Infers the proposition proved by `term`, adding every axiom it depends on
/// to `deps`.
pub(crate) fn infer(
    kernel: &Kernel,
    ctx: &mut Context,
    term: &ProofTerm,
    deps: &mut BTreeSet<String>,
) -> Result<Prop> {
    match term {
        ProofTerm::Var(name) => ctx
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map(|(_, prop)| prop.clone())
            .ok_or_else(|| KernelError::UnboundVariable(name.clone())),

        ProofTerm::Const(name) => {
            let theorem = kernel
                .theorem(name)
                .ok_or_else(|| KernelError::UnknownTheorem(name.clone()))?;
            deps.extend(theorem.axioms().iter().cloned());
            Ok(theorem.prop().clone())
        }

        ProofTerm::Axiom(name) => {
            let axiom = kernel
                .axiom(name)
                .ok_or_else(|| KernelError::UnknownAxiom(name.clone()))?;
            deps.insert(name.clone());
            Ok(axiom.prop.clone())
        }

        ProofTerm::Lam(name, domain, body) => {
            ctx.push((name.clone(), domain.clone()));
            let codomain = infer(kernel, ctx, body, deps);
            ctx.pop();
            Ok(Prop::imp(domain.clone(), codomain?))
        }

        ProofTerm::App(function, argument) => {
            let function_prop = infer(kernel, ctx, function, deps)?;
            match function_prop {
                Prop::Imp(domain, codomain) => {
                    let argument_prop = infer(kernel, ctx, argument, deps)?;
                    if argument_prop != *domain {
                        return Err(KernelError::TypeMismatch {
                            expected: *domain,
                            found: argument_prop,
                        });
                    }
                    Ok(*codomain)
                }
                other => Err(KernelError::NotAFunction(other)),
            }
        }
    }
}
