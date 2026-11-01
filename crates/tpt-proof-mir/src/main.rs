//! MIR access for tpt-proof (SPEC.md §5). This binary runs the compiler front end
//! and reads the MIR of each function. It is the start of `translate.rs`; the
//! verification-condition translation is not built yet.

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

/// Prints each function's name and the number of basic blocks in its optimized MIR.
struct FunctionBlocks;

impl Callbacks for FunctionBlocks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) != DefKind::Fn {
                continue;
            }
            let blocks = tcx.optimized_mir(def_id).basic_blocks.len();
            println!("{} {}", tcx.def_path_str(def_id), blocks);
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
    ];
    compiler_args.extend(args[1..].iter().cloned());
    rustc_driver::compiler_entrypoint(&compiler_args, &mut FunctionBlocks);
}
