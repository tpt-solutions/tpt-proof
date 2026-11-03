//! The `tpt-proof-mir` driver: compiles a file, translates each function in the
//! supported subset to verification conditions, and checks them with Z3.
//!
//! A result of "proved" means Z3 reported `unsat` for the negated VC. It is not
//! a kernel-checked proof unless `TPT_PROOF_VERIFY=1` is set: then Z3 is asked for
//! a proof, the kernel checks it, and "proved (kernel-checked)" is reported
//! (spec.txt §2, Principle 5). Proof mode bypasses the VC cache.
//!
//! The exit status is 0 only if every VC is proved and every function is in the
//! supported subset. Anything else exits with 1, so a failed or unverified function
//! never looks like a success.
//!
//! The solver is set by `TPT_PROOF_Z3` and `TPT_PROOF_TIMEOUT_MS` (see
//! [`SolverConfig::from_lookup`]). `TPT_PROOF_FORMAT=json` prints one JSON object per
//! line, `{"function", "vc", "status", "detail"}`, with `vc` null for a line about
//! the function as a whole. The text form is unchanged.

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
use tpt_proof_contract::smt::{counterexample_values, verify};
use tpt_proof_contract::{Outcome, SolverConfig};
use tpt_proof_mir::translate::translate;

/// Translates and checks every function in the file, counting what is not proved.
struct Verify {
    not_proved: usize,
    cache: VcCache,
    proof_mode: bool,
    config: SolverConfig,
    json: bool,
}

impl Verify {
    /// Prints one result. `vc` is the VC name, or `None` for a line about the
    /// function as a whole. `status` is the machine-readable part of the result.
    fn line(&self, function: &str, vc: Option<&str>, status: &str, detail: &str) {
        if self.json {
            let vc = vc.map_or_else(|| "null".to_string(), json_string);
            println!(
                "{{\"function\":{},\"vc\":{vc},\"status\":{},\"detail\":{}}}",
                json_string(function),
                json_string(status),
                json_string(detail)
            );
        } else {
            println!("{}: {detail}", vc.unwrap_or(function));
        }
    }
}

/// A JSON string literal for `text`.
fn json_string(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl Callbacks for Verify {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) != DefKind::Fn {
                continue;
            }
            let name = tcx.def_path_str(def_id);
            match translate(tcx, def_id) {
                Err(reason) => {
                    self.not_proved += 1;
                    self.line(
                        &name,
                        None,
                        "unsupported",
                        &format!("unsupported: {reason}"),
                    );
                }
                Ok(vcs) if vcs.is_empty() => {
                    self.line(&name, None, "no_assertions", "no assertions");
                }
                Ok(vcs) => {
                    for vc in &vcs {
                        let outcome = if self.proof_mode {
                            verify(vc, &self.config)
                        } else {
                            self.cache.check(vc, &self.config)
                        };
                        if !matches!(outcome, Outcome::SolverUnsat | Outcome::Verified) {
                            self.not_proved += 1;
                        }
                        let (status, verdict) = match outcome {
                            Outcome::SolverUnsat => (
                                "proved",
                                "proved (solver unsat, not kernel-checked)".to_string(),
                            ),
                            Outcome::Verified => ("proved", "proved (kernel-checked)".to_string()),
                            Outcome::Unchecked { reason } => (
                                "unchecked",
                                format!("unchecked (solver unsat, proof not accepted): {reason}"),
                            ),
                            Outcome::Failed { counterexample } => {
                                let values: Vec<String> = counterexample_values(&counterexample)
                                    .into_iter()
                                    .map(|(name, value)| format!("{name} = {value}"))
                                    .collect();
                                (
                                    "counterexample",
                                    format!("counterexample: {}", values.join(", ")),
                                )
                            }
                            Outcome::Timeout => ("timeout", "timeout".to_string()),
                            Outcome::Unknown(reason) => ("unknown", format!("unknown: {reason}")),
                            Outcome::Error(reason) => ("error", format!("error: {reason}")),
                        };
                        self.line(&name, Some(&vc.name), status, &verdict);
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
    let proof_mode = std::env::var("TPT_PROOF_VERIFY").is_ok_and(|value| value == "1");
    let json = std::env::var("TPT_PROOF_FORMAT").is_ok_and(|value| value == "json");
    let config = match SolverConfig::from_lookup(|name| std::env::var(name).ok()) {
        Ok(config) => config,
        Err(message) => {
            eprintln!("tpt-proof-mir: {message}");
            std::process::exit(2);
        }
    };
    let mut driver = Verify {
        not_proved: 0,
        cache,
        proof_mode,
        config,
        json,
    };
    rustc_driver::compiler_entrypoint(&compiler_args, &mut driver);
    if driver.not_proved > 0 {
        std::process::exit(1);
    }
}
