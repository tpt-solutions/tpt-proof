//! Shared test support: detecting the external tools that some tests need.
//!
//! Each test crate includes this file with `#[path]`, because the kernel has no
//! dependencies, not even dev-dependencies, so it cannot share a crate. A test that
//! needs a tool calls [`skip_unless`] first. When the tool is missing the test
//! returns early with a message, so a run without the tool says what was skipped.

use std::process::{Command, Stdio};

/// Whether `program --version` runs successfully.
pub fn available(program: &str) -> bool {
    Command::new(program)
        .arg("--version")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|status| status.success())
        .unwrap_or(false)
}

/// Returns `true`, after printing why, when `program` is missing. A test uses it
/// as `if skip_unless("z3") { return; }`.
pub fn skip_unless(program: &str) -> bool {
    if available(program) {
        false
    } else {
        eprintln!("skipped: `{program}` is not on the PATH");
        true
    }
}
