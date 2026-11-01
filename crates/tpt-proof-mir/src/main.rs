//! The `tpt-proof-mir` driver: compiles a file, translates each function in the
//! supported subset to verification conditions, and checks them with Z3.
//!
//! A result of "proved" means Z3 reported `unsat` for the negated VC. It is not
//! yet a kernel-checked proof (spec.txt §2, Principle 5).
//!
//! The exit status is 0 only if every VC is proved and every function is in the
//! supported subset. Anything else exits with 1, so a failed or unverified function
//! never looks like a success.

#![feature(rustc_private)]
#![forbid(unsafe_code)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use tpt_proof_contract::cache::VcCache;
use tpt_proof_contract::smt::counterexample_values;
use tpt_proof_contract::{Outcome, SolverConfig};
use tpt_proof_mir::translate::translate;

/// Translates and checks every function in the file, counting what is not proved.
struct Verify {
    not_proved: usize,
    cache: VcCache,
}

impl Callbacks for Verify {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let config = SolverConfig::default();
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) != DefKind::Fn {
                continue;
            }
            let name = tcx.def_path_str(def_id);
            match translate(tcx, def_id) {
                Err(reason) => {
                    self.not_proved += 1;
                    println!("{name}: unsupported: {reason}");
                }
                Ok(vcs) if vcs.is_empty() => println!("{name}: no assertions"),
                Ok(vcs) => {
                    for vc in &vcs {
                        let outcome = self.cache.check(vc, &config);
                        if !matches!(outcome, Outcome::SolverUnsat) {
                            self.not_proved += 1;
                        }
                        let verdict = match outcome {
                            Outcome::SolverUnsat => {
                                "proved (solver unsat, not kernel-checked)".to_string()
                            }
                            Outcome::Failed { counterexample } => {
                                let values: Vec<String> = counterexample_values(&counterexample)
                                    .into_iter()
                                    .map(|(name, value)| format!("{name} = {value}"))
                                    .collect();
                                format!("counterexample: {}", values.join(", "))
                            }
                            Outcome::Timeout => "timeout".to_string(),
                            Outcome::Unknown(reason) => format!("unknown: {reason}"),
                            Outcome::Error(reason) => format!("error: {reason}"),
                        };
                        println!("{}: {verdict}", vc.name);
                    }
                }
            }
        }
        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: tpt-proof-mir <file.rs>");
        std::process::exit(2);
    }
    let mut compiler_args = vec![
        "rustc".to_string(),
        "--edition=2021".to_string(),
        "--crate-type=lib".to_string(),
        "--cfg=tpt_proof_verify".to_string(),
    ];
    compiler_args.extend(args[1..].iter().cloned());
    let cache = match std::env::var("TPT_PROOF_CACHE") {
        Ok(directory) => VcCache::in_directory(directory).unwrap_or_else(|_| VcCache::in_memory()),
        Err(_) => VcCache::in_memory(),
    };
    let mut verify = Verify {
        not_proved: 0,
        cache,
    };
    rustc_driver::compiler_entrypoint(&compiler_args, &mut verify);
    if verify.not_proved > 0 {
        std::process::exit(1);
    }
}
