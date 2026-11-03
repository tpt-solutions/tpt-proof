//! The proof checker. It computes the proposition a term proves and collects the
//! axioms it uses. Checking is a plain recursive function over the term.

use std::collections::BTreeSet;

use crate::arith;
use crate::terms::{alpha_eq, ProofTerm, Prop, Sort, Term};
use crate::{taut, Kernel, KernelError, Result};

/// Everything in scope while checking a term.
#[derive(Default)]
pub(crate) struct Context {
    /// Proof variables and their propositions, innermost binding last.
    pub(crate) props: Vec<(String, Prop)>,
    /// Individual variables bound by enclosing `forall`s and their sorts,
    /// innermost last.
    pub(crate) individuals: Vec<(String, Sort)>,
}

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
            .props
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
            kernel.check_prop(domain, &ctx.individuals)?;
            ctx.props.push((name.clone(), domain.clone()));
            let codomain = infer(kernel, ctx, body, deps);
            ctx.props.pop();
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
            reject_reserved_binder(name)?;
            let body_prop = infer(kernel, ctx, body, deps)?;
            // Generalizing over `name` is only valid if nothing the body relies on
            // mentions `name`. Otherwise the proof would be specific to one choice.
            if ctx.props.iter().any(|(_, prop)| prop.has_free(name)) {
                return Err(KernelError::InvalidGeneralization {
                    variable: name.clone(),
                    reason: "a local hypothesis mentions it".to_string(),
                });
            }
            check_deps_do_not_mention(kernel, deps, name, |prop, n| prop.has_free(n))?;
            Ok(Prop::forall(name, body_prop))
        }

        ProofTerm::TyApp(function, argument) => {
            kernel.check_prop(argument, &ctx.individuals)?;
            match infer(kernel, ctx, function, deps)? {
                Prop::Forall(name, body) => Ok(body.substitute(&name, argument)),
                other => Err(KernelError::NotAForall(other)),
            }
        }

        ProofTerm::IndLam(name, sort, body) => {
            reject_reserved_binder(name)?;
            kernel.check_sort(sort)?;
            ctx.individuals.push((name.clone(), sort.clone()));
            let body_prop = infer(kernel, ctx, body, deps);
            ctx.individuals.pop();
            let body_prop = body_prop?;
            // As for TyLam: a hypothesis or an axiom that mentions the variable
            // would make the generalized proof depend on one individual.
            if ctx
                .props
                .iter()
                .any(|(_, prop)| prop.has_free_individual(name))
            {
                return Err(KernelError::InvalidGeneralization {
                    variable: name.clone(),
                    reason: "a local hypothesis mentions it".to_string(),
                });
            }
            check_deps_do_not_mention(kernel, deps, name, |prop, n| prop.has_free_individual(n))?;
            Ok(Prop::forall_sorted(name, sort.clone(), body_prop))
        }

        ProofTerm::IndApp(function, argument) => {
            let function_prop = infer(kernel, ctx, function, deps)?;
            let found = kernel.check_term_in(argument, &ctx.individuals)?;
            match function_prop {
                Prop::ForallInd(name, expected, body) => {
                    if found != expected {
                        return Err(KernelError::SortMismatch { expected, found });
                    }
                    Ok(body.subst_individual(&name, argument))
                }
                other => Err(KernelError::NotForallInd(other)),
            }
        }

        ProofTerm::Refl(term) => {
            kernel.check_term_in(term, &ctx.individuals)?;
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
            let (arg_sorts, _) = kernel
                .signature(symbol)
                .ok_or_else(|| KernelError::UnknownFunction(symbol.clone()))?;
            if arg_sorts.len() != args.len() {
                return Err(KernelError::ArityMismatch {
                    symbol: symbol.clone(),
                    expected: arg_sorts.len(),
                    found: args.len(),
                });
            }
            let mut lefts = Vec::new();
            let mut rights = Vec::new();
            for (arg, expected) in args.iter().zip(&arg_sorts) {
                match infer(kernel, ctx, arg, deps)? {
                    Prop::Eq(left, right) => {
                        for side in [&left, &right] {
                            let found = kernel.check_term_in(side, &ctx.individuals)?;
                            if &found != expected {
                                return Err(KernelError::SortMismatch {
                                    expected: expected.clone(),
                                    found,
                                });
                            }
                        }
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

        ProofTerm::Leibniz(variable, motive, equation, proof) => {
            let (left, right) = match infer(kernel, ctx, equation, deps)? {
                Prop::Eq(left, right) => (left, right),
                other => return Err(KernelError::NotAnEquality(other)),
            };
            let sort = kernel.check_term_in(&left, &ctx.individuals)?;
            let right_sort = kernel.check_term_in(&right, &ctx.individuals)?;
            if right_sort != sort {
                return Err(KernelError::SortMismatch {
                    expected: sort,
                    found: right_sort,
                });
            }
            ctx.individuals.push((variable.clone(), sort));
            let checked = kernel.check_prop(motive, &ctx.individuals);
            ctx.individuals.pop();
            checked?;
            let expected = motive.subst_individual(variable, &left);
            let found = infer(kernel, ctx, proof, deps)?;
            if !alpha_eq(&found, &expected) {
                return Err(KernelError::TypeMismatch { expected, found });
            }
            Ok(motive.subst_individual(variable, &right))
        }

        ProofTerm::Cases(variable, sort, motive, cases) => check_split(
            kernel,
            ctx,
            deps,
            Split {
                variable,
                sort,
                motive,
                cases,
                induction: false,
            },
        ),

        ProofTerm::Induct(variable, sort, motive, cases) => check_split(
            kernel,
            ctx,
            deps,
            Split {
                variable,
                sort,
                motive,
                cases,
                induction: true,
            },
        ),

        ProofTerm::Taut(formula) => {
            taut::check(kernel, formula)?;
            Ok(formula.encode())
        }
    }
}

/// The parts of a case analysis or an induction over an inductive sort.
struct Split<'a> {
    variable: &'a str,
    sort: &'a Sort,
    motive: &'a Prop,
    cases: &'a [ProofTerm],
    /// Whether each case may use a hypothesis for its recursive arguments.
    induction: bool,
}

/// Checks a case analysis (`Cases`) or an induction (`Induct`) and returns the
/// universal proposition it proves.
fn check_split(
    kernel: &Kernel,
    ctx: &mut Context,
    deps: &mut BTreeSet<String>,
    split: Split<'_>,
) -> Result<Prop> {
    let Split {
        variable,
        sort,
        motive,
        cases,
        induction,
    } = split;
    let constructors = kernel
        .constructors(sort)
        .ok_or_else(|| KernelError::NotInductive(sort.0.clone()))?;
    if cases.len() != constructors.len() {
        return Err(KernelError::WrongNumberOfCases {
            sort: sort.clone(),
            expected: constructors.len(),
            found: cases.len(),
        });
    }
    ctx.individuals.push((variable.to_string(), sort.clone()));
    let checked = kernel.check_prop(motive, &ctx.individuals);
    ctx.individuals.pop();
    checked?;
    for ((constructor, _), case) in constructors.iter().zip(cases) {
        let expected = if induction {
            kernel.induction_premise(variable, sort, motive, constructor)?
        } else {
            kernel.case_premise(variable, sort, motive, constructor)?
        };
        let found = infer(kernel, ctx, case, deps)?;
        if !alpha_eq(&found, &expected) {
            return Err(KernelError::TypeMismatch { expected, found });
        }
    }
    // As for IndLam: a hypothesis or an axiom that mentions the variable would
    // make the generalized proof depend on one individual.
    if ctx
        .props
        .iter()
        .any(|(_, prop)| prop.has_free_individual(variable))
    {
        return Err(KernelError::InvalidGeneralization {
            variable: variable.to_string(),
            reason: "a local hypothesis mentions it".to_string(),
        });
    }
    check_deps_do_not_mention(kernel, deps, variable, |prop, n| {
        prop.has_free_individual(n)
    })?;
    Ok(Prop::forall_sorted(variable, sort.clone(), motive.clone()))
}

/// Fails if `name` is a built-in name. Binding one would let a proof
/// generalize over a symbol the rest of the kernel reads with a fixed meaning.
fn reject_reserved_binder(name: &str) -> Result<()> {
    if arith::is_reserved(name) {
        Err(KernelError::ReservedSymbol(name.to_string()))
    } else {
        Ok(())
    }
}

/// Fails if any axiom the proof uses mentions `name`, under `mentions`.
fn check_deps_do_not_mention(
    kernel: &Kernel,
    deps: &BTreeSet<String>,
    name: &str,
    mentions: impl Fn(&Prop, &str) -> bool,
) -> Result<()> {
    for dep in deps {
        let uses = kernel
            .axiom(dep)
            .is_some_and(|axiom| mentions(&axiom.prop, name));
        if uses {
            return Err(KernelError::InvalidGeneralization {
                variable: name.to_string(),
                reason: format!("it uses axiom `{dep}`, which mentions it"),
            });
        }
    }
    Ok(())
}
