//! Command-line interface for tpt-proof.
//!
//! `tpt-proof verify <file.rs>` runs the MIR driver (`tpt-proof-mir`) on a file and
//! prints one verdict per assertion. The driver needs a pinned nightly compiler, so
//! it is a separate binary. It is found through the `TPT_PROOF_MIR` environment
//! variable, or on the PATH.

use std::process::{Command, ExitCode};

const USAGE: &str = "usage: tpt-proof --version | tpt-proof verify <file.rs>";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [flag] if flag == "--version" || flag == "-V" => {
            println!("tpt-proof {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        [command, file] if command == "verify" => verify(file),
        _ => {
            eprintln!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

/// The nightly the driver is built with. It must match `crates/tpt-proof-mir/rust-toolchain.toml`.
const DRIVER_TOOLCHAIN: &str = "nightly-2026-10-31";

/// Runs the MIR driver on `file` through the pinned nightly, so the driver finds its
/// runtime libraries without cargo. `TPT_PROOF_MIR` names the driver binary.
fn verify(file: &str) -> ExitCode {
    let driver = std::env::var("TPT_PROOF_MIR").unwrap_or_else(|_| "tpt-proof-mir".to_string());
    let toolchain =
        std::env::var("TPT_PROOF_TOOLCHAIN").unwrap_or_else(|_| DRIVER_TOOLCHAIN.to_string());
    match Command::new("rustup")
        .args(["run", &toolchain, &driver])
        .arg(file)
        .status()
    {
        Ok(status) if status.success() => ExitCode::SUCCESS,
        Ok(_) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("tpt-proof: could not run rustup for `{driver}`: {error}");
            eprintln!("install rustup and the toolchain `{toolchain}`, or set TPT_PROOF_TOOLCHAIN");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_missing_driver_is_reported_with_a_hint() {
        // A driver path that does not exist: the command fails cleanly, not by panic.
        std::env::set_var("TPT_PROOF_MIR", "definitely-not-a-real-driver-binary");
        assert_ne!(verify("anything.rs"), ExitCode::SUCCESS);
        std::env::remove_var("TPT_PROOF_MIR");
    }
}
