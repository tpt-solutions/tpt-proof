//! The `tpt-proof-mir` driver: compiles a file, translates each function in the
//! supported subset to verification conditions, and checks them with Z3.
//!
//! A result of "proved" means Z3 reported `unsat` for the negated VC. It is not
//! yet a kernel-checked proof (SPEC.md §2, Principle 5).

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
use tpt_proof_contract::{check, Outcome, SolverConfig};
use tpt_proof_mir::translate::translate;

/// Translates and checks every function in the file.
struct Verify;

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
                Err(reason) => println!("{name}: unsupported: {reason}"),
                Ok(vcs) if vcs.is_empty() => println!("{name}: no assertions"),
                Ok(vcs) => {
                    for vc in &vcs {
                        let verdict = match check(vc, &config) {
                            Outcome::SolverUnsat => {
                                "proved (solver unsat, not kernel-checked)".to_string()
                            }
                            Outcome::Failed { counterexample } => {
                                format!("counterexample: {}", counterexample.replace('\n', " "))
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
    rustc_driver::compiler_entrypoint(&compiler_args, &mut Verify);
}
