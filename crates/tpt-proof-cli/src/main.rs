//! Command-line interface for tpt-proof.
//!
//! - `tpt-proof verify <file.rs>` runs the MIR driver (`tpt-proof-mir`) on a file and
//!   prints one verdict per assertion. The driver needs a pinned nightly compiler,
//!   so it is a separate binary, found through `TPT_PROOF_MIR` or on the PATH.
//! - `tpt-proof report <library>` prints the dependency report of a lemma library.
//! - `tpt-proof export <library> [--out <file>]` writes the library's lemmas as Lean.
//! - `tpt-proof doctor` checks the tools that verification needs, and says how to
//!   fix what is missing.
//!
//! Verify options are passed to the driver as environment variables, which the
//! driver reads: `--timeout` sets `TPT_PROOF_TIMEOUT_MS`, `--z3-path` sets
//! `TPT_PROOF_Z3`, and `--json` sets `TPT_PROOF_FORMAT=json`.

use std::process::{Command, ExitCode};

const USAGE: &str = "\
usage: tpt-proof verify <file.rs> [--timeout <ms>] [--z3-path <path>] [--json]
       tpt-proof report <library>
       tpt-proof export <library> [--out <file>]
       tpt-proof doctor
       tpt-proof --version | --help

options:
  --timeout <ms>     solver timeout per VC in milliseconds (default 10000)
  --z3-path <path>   the z3 executable to run (default: z3 on the PATH)
  --json             print one JSON object per result, one per line
  --out <file>       write the Lean export to a file instead of standard output
  -h, --help         show this help
  -V, --version      show the version";

/// What the command line asks for, after parsing.
#[derive(Debug, PartialEq, Eq)]
enum Request {
    Help,
    Version,
    Verify {
        file: String,
        timeout_ms: Option<String>,
        z3_path: Option<String>,
        json: bool,
    },
    Report {
        library: String,
    },
    Export {
        library: String,
        out: Option<String>,
    },
    Doctor,
}

/// Parses the arguments after the program name. An error is a message for the user.
fn parse(args: &[String]) -> Result<Request, String> {
    let mut positional = Vec::new();
    let mut timeout_ms = None;
    let mut z3_path = None;
    let mut json = false;
    let mut out = None;
    let mut help = false;
    let mut version = false;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "-h" | "--help" => help = true,
            "-V" | "--version" => version = true,
            "--json" => json = true,
            "--timeout" => {
                let value = iter
                    .next()
                    .ok_or("--timeout needs a value in milliseconds")?;
                timeout_ms = Some(value.clone());
            }
            "--z3-path" => {
                let value = iter.next().ok_or("--z3-path needs a path")?;
                z3_path = Some(value.clone());
            }
            "--out" => {
                let value = iter.next().ok_or("--out needs a file name")?;
                out = Some(value.clone());
            }
            flag if flag.starts_with("--") => return Err(format!("unknown option `{flag}`")),
            _ => positional.push(arg.clone()),
        }
    }
    if help {
        return Ok(Request::Help);
    }
    if version {
        return Ok(Request::Version);
    }
    let verify_only = timeout_ms.is_some() || z3_path.is_some() || json;
    let export_only = out.is_some();
    match positional.as_slice() {
        [command, file] if command == "verify" => Ok(Request::Verify {
            file: file.clone(),
            timeout_ms,
            z3_path,
            json,
        }),
        [_, _] if verify_only => Err("--timeout, --z3-path and --json belong to `verify`".into()),
        [command, library] if command == "report" => {
            if export_only {
                return Err("--out belongs to `export`".into());
            }
            Ok(Request::Report {
                library: library.clone(),
            })
        }
        [command, library] if command == "export" => Ok(Request::Export {
            library: library.clone(),
            out,
        }),
        [command] if command == "doctor" => Ok(Request::Doctor),
        _ => Err(
            "expected `verify <file.rs>`, `report <library>`, `export <library>` or `doctor`"
                .into(),
        ),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match parse(&args) {
        Ok(Request::Help) => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        Ok(Request::Version) => {
            println!("tpt-proof {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Ok(Request::Verify {
            file,
            timeout_ms,
            z3_path,
            json,
        }) => verify(&file, timeout_ms.as_deref(), z3_path.as_deref(), json),
        Ok(Request::Report { library }) => report(&library),
        Ok(Request::Export { library, out }) => export_library(&library, out.as_deref()),
        Ok(Request::Doctor) => doctor(),
        Err(message) => {
            eprintln!("tpt-proof: {message}");
            eprintln!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

/// The nightly the driver is built with. It must match `crates/tpt-proof-mir/rust-toolchain.toml`.
const DRIVER_TOOLCHAIN: &str = "nightly-2026-10-31";

/// Runs the MIR driver on `file` through the pinned nightly, so the driver finds its
/// runtime libraries without cargo. `TPT_PROOF_MIR` names the driver binary.
fn verify(file: &str, timeout_ms: Option<&str>, z3_path: Option<&str>, json: bool) -> ExitCode {
    let driver = driver_name();
    let toolchain = toolchain_name();
    let mut command = Command::new("rustup");
    command.args(["run", &toolchain, &driver]).arg(file);
    if let Some(ms) = timeout_ms {
        command.env("TPT_PROOF_TIMEOUT_MS", ms);
    }
    if let Some(path) = z3_path {
        command.env("TPT_PROOF_Z3", path);
    }
    if json {
        command.env("TPT_PROOF_FORMAT", "json");
    }
    match command.status() {
        Ok(status) if status.success() => ExitCode::SUCCESS,
        Ok(_) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("tpt-proof: could not run rustup for `{driver}`: {error}");
            eprintln!("install rustup and the toolchain `{toolchain}`, or set TPT_PROOF_TOOLCHAIN");
            ExitCode::from(2)
        }
    }
}

fn driver_name() -> String {
    std::env::var("TPT_PROOF_MIR").unwrap_or_else(|_| "tpt-proof-mir".to_string())
}

fn toolchain_name() -> String {
    std::env::var("TPT_PROOF_TOOLCHAIN").unwrap_or_else(|_| DRIVER_TOOLCHAIN.to_string())
}

/// Loads a lemma library, or explains why it cannot be read.
fn read_library(
    path: &str,
) -> Result<(tpt_proof::prelude::Kernel, Vec<tpt_proof::library::Lemma>), String> {
    let source =
        std::fs::read_to_string(path).map_err(|error| format!("cannot read `{path}`: {error}"))?;
    tpt_proof::library::load_with_lemmas(&source).map_err(|error| format!("`{path}`: {error}"))
}

/// Prints the dependency report of a lemma library.
fn report(path: &str) -> ExitCode {
    match read_library(path) {
        Ok((kernel, _)) => {
            print!("{}", tpt_proof::report::dependency_report(&kernel));
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("tpt-proof: {message}");
            ExitCode::FAILURE
        }
    }
}

/// Writes the lemmas of a library as a Lean file, to standard output or `out`.
fn export_library(path: &str, out: Option<&str>) -> ExitCode {
    let (kernel, lemmas) = match read_library(path) {
        Ok(loaded) => loaded,
        Err(message) => {
            eprintln!("tpt-proof: {message}");
            return ExitCode::FAILURE;
        }
    };
    let lemmas: Vec<tpt_proof_export::Lemma> = lemmas
        .into_iter()
        .map(|lemma| tpt_proof_export::Lemma {
            name: lemma.name,
            prop: lemma.prop,
            proof: lemma.proof,
        })
        .collect();
    let text = match tpt_proof_export::export(&kernel, &lemmas) {
        Ok(text) => text,
        Err(error) => {
            eprintln!("tpt-proof: cannot export `{path}` to Lean: {error}");
            return ExitCode::FAILURE;
        }
    };
    match out {
        Some(file) => match std::fs::write(file, text) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("tpt-proof: cannot write `{file}`: {error}");
                ExitCode::FAILURE
            }
        },
        None => {
            print!("{text}");
            ExitCode::SUCCESS
        }
    }
}

/// One tool check: whether it ran, what it reported, and how to fix it if not.
struct Check {
    name: &'static str,
    /// Whether verification cannot run without this tool.
    required: bool,
    result: Result<String, String>,
    fix: &'static str,
}

/// The first line of a command's standard output, or why it could not run.
fn first_line(command: &mut Command) -> Result<String, String> {
    match command.output() {
        Ok(output) if output.status.success() => Ok(String::from_utf8_lossy(&output.stdout)
            .lines()
            .next()
            .unwrap_or("")
            .trim()
            .to_string()),
        Ok(output) => Err(format!("exited with {}", output.status)),
        Err(error) => Err(error.to_string()),
    }
}

/// Checks the tools that verification needs, and prints a line for each.
fn doctor() -> ExitCode {
    let z3 = std::env::var("TPT_PROOF_Z3").unwrap_or_else(|_| "z3".to_string());
    let toolchain = toolchain_name();
    let driver = driver_name();
    let checks = [
        Check {
            name: "rustup",
            required: true,
            result: first_line(Command::new("rustup").arg("--version")),
            fix: "install rustup from https://rustup.rs",
        },
        Check {
            name: "toolchain",
            required: true,
            result: first_line(Command::new("rustup").args(["run", &toolchain, "rustc", "--version"])),
            fix: "rustup toolchain install <toolchain> --component rustc-dev --component llvm-tools-preview",
        },
        Check {
            name: "z3",
            required: true,
            result: first_line(Command::new(&z3).arg("--version")),
            fix: "install Z3 and put it on the PATH, or set TPT_PROOF_Z3 or --z3-path",
        },
        Check {
            name: "driver",
            required: true,
            result: driver_check(&driver),
            fix: "build crates/tpt-proof-mir with `cargo build` and set TPT_PROOF_MIR to the binary",
        },
        Check {
            name: "lean",
            required: false,
            result: first_line(Command::new("lean").arg("--version")),
            fix: "install Lean 4 to check exported proofs with `lean` (optional)",
        },
    ];
    let mut all_required_ok = true;
    for check in &checks {
        match &check.result {
            Ok(detail) => println!("[ok]      {}: {detail}", check.name),
            Err(problem) => {
                if check.required {
                    all_required_ok = false;
                }
                let label = if check.required {
                    "missing"
                } else {
                    "optional"
                };
                println!("[{label}] {}: {problem}. Fix: {}", check.name, check.fix);
            }
        }
    }
    if all_required_ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// The driver is found by path when `TPT_PROOF_MIR` names one, and otherwise on the PATH.
/// Its own `--version` is not available, so a found driver is reported by its path.
fn driver_check(driver: &str) -> Result<String, String> {
    let path = std::path::Path::new(driver);
    if path.is_file() {
        return Ok(format!("found at {}", path.display()));
    }
    if std::env::var("TPT_PROOF_MIR").is_ok() {
        return Err(format!("`{driver}` does not exist"));
    }
    Err(format!("`{driver}` is not set and not on the PATH"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn verify_takes_a_file_and_the_options() {
        let request = parse(&args(&[
            "verify",
            "lib.rs",
            "--timeout",
            "500",
            "--z3-path",
            "C:/z3.exe",
            "--json",
        ]))
        .expect("valid");
        assert_eq!(
            request,
            Request::Verify {
                file: "lib.rs".to_string(),
                timeout_ms: Some("500".to_string()),
                z3_path: Some("C:/z3.exe".to_string()),
                json: true,
            }
        );
    }

    #[test]
    fn options_may_come_before_the_command() {
        let request = parse(&args(&["--json", "verify", "lib.rs"])).expect("valid");
        assert!(matches!(request, Request::Verify { json: true, .. }));
    }

    #[test]
    fn help_and_version_need_no_file() {
        assert_eq!(parse(&args(&["--help"])), Ok(Request::Help));
        assert_eq!(parse(&args(&["-V"])), Ok(Request::Version));
    }

    #[test]
    fn a_flag_without_its_value_is_an_error() {
        assert!(parse(&args(&["verify", "lib.rs", "--timeout"])).is_err());
        assert!(parse(&args(&["verify", "lib.rs", "--z3-path"])).is_err());
        assert!(parse(&args(&["export", "lib", "--out"])).is_err());
    }

    #[test]
    fn unknown_options_and_missing_files_are_errors() {
        assert!(parse(&args(&["verify", "lib.rs", "--fast"])).is_err());
        assert!(parse(&args(&["verify"])).is_err());
        assert!(parse(&args(&[])).is_err());
    }

    #[test]
    fn report_and_export_take_a_library() {
        assert_eq!(
            parse(&args(&["report", "lib.txt"])),
            Ok(Request::Report {
                library: "lib.txt".to_string()
            })
        );
        assert_eq!(
            parse(&args(&["export", "lib.txt", "--out", "out.lean"])),
            Ok(Request::Export {
                library: "lib.txt".to_string(),
                out: Some("out.lean".to_string()),
            })
        );
        assert_eq!(parse(&args(&["doctor"])), Ok(Request::Doctor));
    }

    #[test]
    fn options_are_only_accepted_by_the_command_they_belong_to() {
        assert!(parse(&args(&["report", "lib.txt", "--json"])).is_err());
        assert!(parse(&args(&["report", "lib.txt", "--out", "x"])).is_err());
    }

    #[test]
    fn a_missing_driver_is_reported_with_a_hint() {
        // A driver path that does not exist: the command fails cleanly, not by panic.
        std::env::set_var("TPT_PROOF_MIR", "definitely-not-a-real-driver-binary");
        assert_ne!(verify("anything.rs", None, None, false), ExitCode::SUCCESS);
        std::env::remove_var("TPT_PROOF_MIR");
    }

    #[test]
    fn a_missing_library_is_reported_not_panicked() {
        assert_ne!(
            report("definitely-not-a-real-library.txt"),
            ExitCode::SUCCESS
        );
    }
}
