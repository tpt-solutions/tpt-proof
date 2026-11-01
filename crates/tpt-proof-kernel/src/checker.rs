//! The proof checker. It computes the proposition a term proves and collects the
//! axioms it uses. Checking is a plain recursive function over the term.

use std::collections::BTreeSet;

use crate::terms::{alpha_eq, ProofTerm, Prop, Term};
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
                    if !alpha_eq(&argument_prop, &domain) {
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

        ProofTerm::TyLam(name, body) => {
            let body_prop = infer(kernel, ctx, body, deps)?;
            // Generalizing over `name` is only valid if nothing the body relies on
            // mentions `name`. Otherwise the proof would be specific to one choice.
            if ctx.iter().any(|(_, prop)| prop.has_free(name)) {
                return Err(KernelError::InvalidGeneralization {
                    variable: name.clone(),
                    reason: "a local hypothesis mentions it".to_string(),
                });
            }
            for dep in deps.iter() {
                let mentions = kernel
                    .axiom(dep)
                    .is_some_and(|axiom| axiom.prop.has_free(name));
                if mentions {
                    return Err(KernelError::InvalidGeneralization {
                        variable: name.clone(),
                        reason: format!("it uses axiom `{dep}`, which mentions it"),
                    });
                }
            }
            Ok(Prop::forall(name, body_prop))
        }

        ProofTerm::TyApp(function, argument) => match infer(kernel, ctx, function, deps)? {
            Prop::Forall(name, body) => Ok(body.substitute(&name, argument)),
            other => Err(KernelError::NotAForall(other)),
        },

        ProofTerm::Refl(term) => {
            kernel.check_term(term)?;
            Ok(Prop::Eq(term.clone(), term.clone()))
        }

        ProofTerm::Sym(proof) => match infer(kernel, ctx, proof, deps)? {
            Prop::Eq(left, right) => Ok(Prop::Eq(right, left)),
            other => Err(KernelError::NotAnEquality(other)),
        },

        ProofTerm::Trans(first, second) => {
            let first_prop = infer(kernel, ctx, first, deps)?;
            let second_prop = infer(kernel, ctx, second, deps)?;
            let (left, middle) = match first_prop {
                Prop::Eq(left, middle) => (left, middle),
                other => return Err(KernelError::NotAnEquality(other)),
            };
            let (middle_again, right) = match second_prop {
                Prop::Eq(middle_again, right) => (middle_again, right),
                other => return Err(KernelError::NotAnEquality(other)),
            };
            if middle != middle_again {
                return Err(KernelError::TransitivityMismatch {
                    middle,
                    found: middle_again,
                });
            }
            Ok(Prop::Eq(left, right))
        }

        ProofTerm::Cong(symbol, args) => {
            let arity = kernel
                .arity(symbol)
                .ok_or_else(|| KernelError::UnknownFunction(symbol.clone()))?;
            if arity != args.len() {
                return Err(KernelError::ArityMismatch {
                    symbol: symbol.clone(),
                    expected: arity,
                    found: args.len(),
                });
            }
            let mut lefts = Vec::new();
            let mut rights = Vec::new();
            for arg in args {
                match infer(kernel, ctx, arg, deps)? {
                    Prop::Eq(left, right) => {
                        lefts.push(left);
                        rights.push(right);
                    }
                    other => return Err(KernelError::NotAnEquality(other)),
                }
            }
            Ok(Prop::Eq(
                Term::app(symbol, lefts),
                Term::app(symbol, rights),
            ))
        }
    }
}
