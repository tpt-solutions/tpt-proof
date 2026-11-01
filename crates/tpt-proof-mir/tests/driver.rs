//! The driver reads optimized MIR from a real compilation. These checks run the
//! built binary on a fixture and compare what it reports.

use std::process::Command;

fn run_on(fixture: &str) -> String {
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

fn blocks_of(report: &str, name: &str) -> Option<usize> {
    report.lines().find_map(|line| {
        let mut parts = line.split_whitespace();
        (parts.next()? == name).then(|| parts.next()?.parse().ok())?
    })
}

#[test]
fn reports_every_function_with_its_block_count() {
    let report = run_on("sample.rs");
    assert!(blocks_of(&report, "straight").is_some(), "{report}");
    assert!(blocks_of(&report, "branch").is_some(), "{report}");
    assert!(blocks_of(&report, "looping").is_some(), "{report}");
}

#[test]
fn a_branch_has_more_blocks_than_straight_line_code() {
    let report = run_on("sample.rs");
    let straight = blocks_of(&report, "straight").expect("straight reported");
    let branch = blocks_of(&report, "branch").expect("branch reported");
    assert!(branch > straight, "branch {branch} vs straight {straight}");
}

#[test]
fn a_loop_has_more_blocks_than_a_branch() {
    let report = run_on("sample.rs");
    let branch = blocks_of(&report, "branch").expect("branch reported");
    let looping = blocks_of(&report, "looping").expect("looping reported");
    assert!(looping > branch, "looping {looping} vs branch {branch}");
}
