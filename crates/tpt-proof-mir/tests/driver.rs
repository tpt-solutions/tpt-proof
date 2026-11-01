//! End-to-end checks: the built `tpt-proof-mir` binary translates each fixture's
//! functions and reports a verdict per assertion, or "unsupported". These tests
//! need `z3` on the PATH, since assertions are checked with the solver.

use std::process::Command;

fn verdicts_for(fixture: &str) -> String {
    let manifest = env!("CARGO_MANIFEST_DIR");
    let output = Command::new(env!("CARGO_BIN_EXE_tpt-proof-mir"))
        .arg(format!("{manifest}/tests/fixtures/{fixture}"))
        .output()
        .expect("run the driver");
    assert!(
        output.status.success(),
        "driver failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn line_for<'a>(report: &'a str, function: &str) -> &'a str {
    report
        .lines()
        .find(|line| line.starts_with(&format!("{function}:")))
        .unwrap_or_else(|| panic!("no line for {function} in:\n{report}"))
}

#[test]
fn an_overflowing_addition_gets_a_counterexample() {
    let report = verdicts_for("overflow_unsafe.rs");
    let line = line_for(&report, "add");
    assert!(line.contains("counterexample"), "{line}");
    assert!(line.contains("_1") && line.contains("_2"), "{line}");
}

#[test]
fn a_guarded_addition_is_proved_under_its_branch() {
    let report = verdicts_for("overflow_safe.rs");
    let line = line_for(&report, "bump_small");
    assert!(line.contains("proved"), "{line}");
}

#[test]
fn signed_subtraction_can_overflow_at_the_minimum() {
    let report = verdicts_for("signed_diff.rs");
    let line = line_for(&report, "diff");
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn multiplication_is_reported_as_unsupported() {
    let report = verdicts_for("unsupported_mul.rs");
    let line = line_for(&report, "mul");
    assert!(line.contains("unsupported"), "{line}");
}

#[test]
fn loops_are_reported_as_unsupported() {
    let report = verdicts_for("unsupported_loop.rs");
    let line = line_for(&report, "count");
    assert!(
        line.contains("unsupported") && line.contains("loops"),
        "{line}"
    );
}

fn lines_for<'a>(report: &'a str, function: &str) -> Vec<&'a str> {
    report
        .lines()
        .filter(|line| line.starts_with(&format!("{function}:")))
        .collect()
}

#[test]
fn a_contract_is_assumed_and_its_postcondition_proved() {
    let report = verdicts_for("contract_ok.rs");
    let lines = lines_for(&report, "plus100");
    assert_eq!(lines.len(), 2, "{report}");
    assert!(lines.iter().all(|line| line.contains("proved")), "{report}");
}

#[test]
fn a_postcondition_that_does_not_follow_gets_a_counterexample() {
    let report = verdicts_for("contract_ensures_fails.rs");
    let ensures = lines_for(&report, "plus100_loose")
        .into_iter()
        .find(|line| line.contains("ensures"))
        .unwrap_or_else(|| panic!("no ensures line in:\n{report}"));
    assert!(ensures.contains("counterexample"), "{ensures}");
}

#[test]
fn a_contract_outside_the_language_is_reported_not_ignored() {
    let report = verdicts_for("contract_bad_syntax.rs");
    let line = line_for(&report, "bad");
    assert!(
        line.contains("unsupported") && line.contains("requires"),
        "{line}"
    );
}

#[test]
fn macro_expanded_contracts_are_verified_through_the_cfg_split() {
    let report = verdicts_for("contract_expanded.rs");
    let ensures = lines_for(&report, "plus100_loose")
        .into_iter()
        .find(|line| line.contains("ensures"))
        .unwrap_or_else(|| panic!("no ensures line in:\n{report}"));
    assert!(ensures.contains("counterexample"), "{ensures}");
    assert!(!report.contains("unsupported"), "{report}");
}
