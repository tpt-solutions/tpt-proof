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
        matches!(output.status.code(), Some(0) | Some(1)),
        "driver failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// The driver's exit status for a fixture.
fn exit_code_for(fixture: &str) -> Option<i32> {
    let manifest = env!("CARGO_MANIFEST_DIR");
    Command::new(env!("CARGO_BIN_EXE_tpt-proof-mir"))
        .arg(format!("{manifest}/tests/fixtures/{fixture}"))
        .output()
        .expect("run the driver")
        .status
        .code()
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
fn two_parameter_multiplication_can_overflow() {
    let report = verdicts_for("unsupported_mul.rs");
    let line = line_for(&report, "mul");
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn loops_without_invariants_are_reported_as_unsupported() {
    let report = verdicts_for("unsupported_loop.rs");
    let line = line_for(&report, "count");
    assert!(
        line.contains("unsupported") && line.contains("no invariant"),
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

#[test]
fn a_loop_with_a_correct_invariant_is_fully_proved() {
    let report = verdicts_for("loop_verified.rs");
    let lines = lines_for(&report, "count_up");
    assert!(lines.len() >= 5, "{report}");
    assert!(lines.iter().all(|line| line.contains("proved")), "{report}");
    assert!(
        lines
            .iter()
            .any(|line| line.contains("invariant is preserved")),
        "{report}"
    );
}

#[test]
fn a_loop_invariant_that_fails_on_entry_gets_a_counterexample() {
    let report = verdicts_for("loop_wrong_invariant.rs");
    let entry = lines_for(&report, "count_wrong")
        .into_iter()
        .find(|line| line.contains("holds on entry"))
        .unwrap_or_else(|| panic!("no entry line in:\n{report}"));
    assert!(entry.contains("counterexample"), "{entry}");
}

#[test]
fn a_loop_invariant_that_is_not_preserved_gets_a_counterexample() {
    let report = verdicts_for("loop_preservation_fails.rs");
    let preserved = lines_for(&report, "count_bounded")
        .into_iter()
        .find(|line| line.contains("preserved"))
        .unwrap_or_else(|| panic!("no preservation line in:\n{report}"));
    assert!(preserved.contains("counterexample"), "{preserved}");
}

#[test]
fn a_loop_without_an_invariant_is_reported_with_its_line() {
    let report = verdicts_for("loop_no_invariant.rs");
    let line = line_for(&report, "count_none");
    assert!(
        line.contains("unsupported") && line.contains("no invariant"),
        "{line}"
    );
}

#[test]
fn an_overflowing_multiplication_gets_a_counterexample() {
    let report = verdicts_for("mul_overflow.rs");
    let line = line_for(&report, "double");
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn a_guarded_multiplication_is_proved_under_its_branch() {
    let report = verdicts_for("mul_guarded.rs");
    let lines = lines_for(&report, "double_small");
    assert!(!lines.is_empty(), "{report}");
    assert!(lines.iter().all(|line| line.contains("proved")), "{report}");
}

#[test]
fn an_unguarded_division_gets_a_zero_divisor_counterexample() {
    let report = verdicts_for("div_unguarded.rs");
    let line = line_for(&report, "quotient");
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn a_guarded_division_is_proved_and_its_result_is_bounded() {
    let report = verdicts_for("div_guarded.rs");
    let lines = lines_for(&report, "quotient_guarded");
    assert!(lines.len() >= 3, "{report}");
    assert!(lines.iter().all(|line| line.contains("proved")), "{report}");
}

#[test]
fn signed_remainder_is_translated_and_its_assertions_proved() {
    let report = verdicts_for("rem_signed.rs");
    let line = line_for(&report, "remainder");
    assert!(
        !line.contains("unsupported") && line.contains("proved"),
        "{line}"
    );
}

#[test]
fn a_caller_meets_the_callee_precondition_and_inherits_its_postcondition() {
    let report = verdicts_for("call_verified.rs");
    let lines = lines_for(&report, "caller");
    assert!(lines.len() >= 2, "{report}");
    assert!(lines.iter().all(|line| line.contains("proved")), "{report}");
    assert!(
        lines.iter().any(|line| line.contains("precondition")),
        "{report}"
    );
}

#[test]
fn a_call_that_violates_the_callee_precondition_gets_a_counterexample() {
    let report = verdicts_for("call_violated.rs");
    let line = lines_for(&report, "careless")
        .into_iter()
        .find(|line| line.contains("precondition"))
        .unwrap_or_else(|| panic!("no precondition line in:\n{report}"));
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn an_uncontracted_callee_gives_an_unknown_result() {
    let report = verdicts_for("call_uncontracted.rs");
    let line = lines_for(&report, "caller_expects_more")
        .into_iter()
        .find(|line| line.contains("ensures"))
        .unwrap_or_else(|| panic!("no ensures line in:\n{report}"));
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn signed_division_and_remainder_truncate_toward_zero() {
    let report = verdicts_for("signed_semantics.rs");
    let division = lines_for(&report, "div_case");
    let remainder = lines_for(&report, "rem_case");
    assert!(!division.is_empty() && !remainder.is_empty(), "{report}");
    assert!(
        division
            .iter()
            .chain(&remainder)
            .all(|line| line.contains("proved")),
        "{report}"
    );
}

#[test]
fn a_euclidean_claim_for_signed_division_is_refuted() {
    let report = verdicts_for("signed_euclid_wrong.rs");
    assert!(
        lines_for(&report, "div_euclid_claim")
            .iter()
            .any(|line| line.contains("ensures") && line.contains("counterexample")),
        "{report}"
    );
}

#[test]
fn signed_division_checks_zero_and_the_minimum_over_minus_one() {
    let report = verdicts_for("signed_overflow.rs");
    let lines = lines_for(&report, "divide");
    assert!(lines.len() >= 2, "{report}");
    assert!(
        lines.iter().all(|line| line.contains("counterexample")),
        "{report}"
    );
}

#[test]
fn overflow_through_a_shared_reference_gets_a_counterexample() {
    let report = verdicts_for("ref_overflow.rs");
    let line = line_for(&report, "bump_ref");
    assert!(line.contains("counterexample"), "{line}");
}

#[test]
fn a_postcondition_through_a_shared_reference_is_proved() {
    let report = verdicts_for("ref_ensures.rs");
    let lines = lines_for(&report, "bump_checked");
    assert!(lines.len() >= 2, "{report}");
    assert!(lines.iter().all(|line| line.contains("proved")), "{report}");
}

#[test]
fn a_borrow_of_a_local_reads_its_value() {
    let report = verdicts_for("ref_borrow.rs");
    let line = line_for(&report, "read_back");
    assert!(line.contains("proved"), "{line}");
}

#[test]
fn mutable_references_are_reported_as_unsupported() {
    let report = verdicts_for("mut_ref_unsupported.rs");
    let line = line_for(&report, "set");
    assert!(
        line.contains("unsupported") && line.contains("mutable"),
        "{line}"
    );
}

#[test]
fn cell_references_are_reported_as_unsupported() {
    let report = verdicts_for("cell_unsupported.rs");
    let line = line_for(&report, "get");
    assert!(line.contains("unsupported"), "{line}");
}

#[test]
fn the_exit_status_is_zero_only_when_everything_is_proved() {
    assert_eq!(exit_code_for("ref_ensures.rs"), Some(0));
    assert_eq!(exit_code_for("ref_overflow.rs"), Some(1));
    assert_eq!(exit_code_for("mut_ref_unsupported.rs"), Some(1));
}
