//! SMT-LIB encoding of verification conditions and the Z3 driver.
//!
//! The solver is untrusted (spec.txt §7). A solver `unsat` answer means the
//! negated goal is unsatisfiable, but it is not yet a checked proof. That is why
//! [`crate::Outcome::SolverUnsat`] is not `Verified`.

use std::fmt;
use std::io::{Read as _, Write as _};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use crate::reflect;
use crate::vc::{Expr, Sort, Vc};
use crate::Outcome;

/// Errors found before the solver runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodeError {
    /// A variable name that is not a plain SMT-LIB symbol.
    InvalidName(String),
    /// A variable used but not declared.
    UndeclaredVariable(String),
    /// A term used at the wrong sort, such as `true + 1`.
    SortMismatch {
        /// The sort the position requires.
        expected: Sort,
        /// The sort of the term found there.
        found: Sort,
    },
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeError::InvalidName(name) => write!(f, "`{name}` is not a valid variable name"),
            EncodeError::UndeclaredVariable(name) => write!(f, "variable `{name}` is not declared"),
            EncodeError::SortMismatch { expected, found } => {
                write!(f, "expected a {expected:?} term, found {found:?}")
            }
        }
    }
}

impl std::error::Error for EncodeError {}

/// Checks the VC, then encodes it as an SMT-LIB 2 script. The script asserts the
/// assumptions and the negated goal, so `unsat` means the goal is valid.
pub fn encode(vc: &Vc) -> Result<String, EncodeError> {
    render_script(vc, false)
}

/// Like [`encode`], but the script asks Z3 for a proof of `unsat` instead of a
/// model. The proof is checked by [`crate::reflect::reconstruct`].
pub fn encode_with_proof(vc: &Vc) -> Result<String, EncodeError> {
    render_script(vc, true)
}

fn render_script(vc: &Vc, proof: bool) -> Result<String, EncodeError> {
    let mut env: Vec<(&str, Sort)> = Vec::new();
    for (name, sort) in &vc.vars {
        if !is_simple_symbol(name) {
            return Err(EncodeError::InvalidName(name.clone()));
        }
        env.push((name, *sort));
    }
    for assumption in &vc.assumptions {
        expect_sort(assumption, Sort::Bool, &env)?;
    }
    expect_sort(&vc.goal, Sort::Bool, &env)?;

    let mut script = String::new();
    if proof {
        script.push_str("(set-option :produce-proofs true)\n");
    }
    script.push_str("(set-logic ALL)\n");
    for (name, sort) in &vc.vars {
        let sort = match sort {
            Sort::Int => "Int",
            Sort::Bool => "Bool",
        };
        script.push_str(&format!("(declare-const {name} {sort})\n"));
    }
    for assumption in &vc.assumptions {
        script.push_str(&format!("(assert {})\n", render(assumption)));
    }
    script.push_str(&format!("(assert (not {}))\n", render(&vc.goal)));
    if proof {
        script.push_str("(check-sat)\n(get-proof)\n");
    } else {
        script.push_str("(check-sat)\n(get-model)\n");
    }
    Ok(script)
}

fn is_simple_symbol(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn render(expr: &Expr) -> String {
    match expr {
        Expr::Int(n) if *n < 0 => format!("(- {})", n.unsigned_abs()),
        Expr::Int(n) => n.to_string(),
        Expr::Bool(true) => "true".to_string(),
        Expr::Bool(false) => "false".to_string(),
        Expr::Var(name) => name.clone(),
        Expr::Add(a, b) => binary("+", a, b),
        Expr::Sub(a, b) => binary("-", a, b),
        Expr::Mul(a, b) => binary("*", a, b),
        Expr::Div(a, b) => binary("div", a, b),
        Expr::Rem(a, b) => binary("mod", a, b),
        Expr::Ite(c, a, b) => format!("(ite {} {} {})", render(c), render(a), render(b)),
        Expr::Lt(a, b) => binary("<", a, b),
        Expr::Le(a, b) => binary("<=", a, b),
        Expr::Eq(a, b) => binary("=", a, b),
        Expr::Not(a) => format!("(not {})", render(a)),
        Expr::And(items) => nary("and", items, "true"),
        Expr::Or(items) => nary("or", items, "false"),
        Expr::Implies(a, b) => binary("=>", a, b),
    }
}

fn binary(op: &str, a: &Expr, b: &Expr) -> String {
    format!("({op} {} {})", render(a), render(b))
}

fn nary(op: &str, items: &[Expr], empty: &str) -> String {
    match items {
        [] => empty.to_string(),
        [single] => render(single),
        _ => {
            let parts: Vec<String> = items.iter().map(render).collect();
            format!("({op} {})", parts.join(" "))
        }
    }
}

/// Returns the sort of `expr`, checking every subterm, or an error.
fn sort_of(expr: &Expr, env: &[(&str, Sort)]) -> Result<Sort, EncodeError> {
    let lookup = |name: &str| {
        env.iter()
            .rev()
            .find(|(bound, _)| *bound == name)
            .map(|(_, sort)| *sort)
            .ok_or_else(|| EncodeError::UndeclaredVariable(name.to_string()))
    };
    match expr {
        Expr::Int(_) => Ok(Sort::Int),
        Expr::Bool(_) => Ok(Sort::Bool),
        Expr::Var(name) => lookup(name),
        Expr::Ite(c, a, b) => {
            expect_sort(c, Sort::Bool, env)?;
            let sort = sort_of(a, env)?;
            expect_sort(b, sort, env)?;
            Ok(sort)
        }
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Rem(a, b) => {
            expect_sort(a, Sort::Int, env)?;
            expect_sort(b, Sort::Int, env)?;
            Ok(Sort::Int)
        }
        Expr::Lt(a, b) | Expr::Le(a, b) => {
            expect_sort(a, Sort::Int, env)?;
            expect_sort(b, Sort::Int, env)?;
            Ok(Sort::Bool)
        }
        Expr::Eq(a, b) => {
            let sort = sort_of(a, env)?;
            expect_sort(b, sort, env)?;
            Ok(Sort::Bool)
        }
        Expr::Not(a) => {
            expect_sort(a, Sort::Bool, env)?;
            Ok(Sort::Bool)
        }
        Expr::And(items) | Expr::Or(items) => {
            for item in items {
                expect_sort(item, Sort::Bool, env)?;
            }
            Ok(Sort::Bool)
        }
        Expr::Implies(a, b) => {
            expect_sort(a, Sort::Bool, env)?;
            expect_sort(b, Sort::Bool, env)?;
            Ok(Sort::Bool)
        }
    }
}

fn expect_sort(expr: &Expr, expected: Sort, env: &[(&str, Sort)]) -> Result<(), EncodeError> {
    let found = sort_of(expr, env)?;
    if found == expected {
        Ok(())
    } else {
        Err(EncodeError::SortMismatch { expected, found })
    }
}

/// Settings for running the solver.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Path to the `z3` executable.
    pub z3: PathBuf,
    /// Per-query timeout in milliseconds.
    pub timeout_ms: u64,
}

impl SolverConfig {
    /// The configuration named by `TPT_PROOF_Z3` (the solver path) and
    /// `TPT_PROOF_TIMEOUT_MS` (the timeout), with the defaults for unset names.
    /// `lookup` reads a variable, so the function needs no process environment.
    pub fn from_lookup(lookup: impl Fn(&str) -> Option<String>) -> Result<SolverConfig, String> {
        let mut config = SolverConfig::default();
        if let Some(path) = lookup("TPT_PROOF_Z3") {
            config.z3 = PathBuf::from(path);
        }
        if let Some(text) = lookup("TPT_PROOF_TIMEOUT_MS") {
            config.timeout_ms = match text.trim().parse::<u64>() {
                Ok(ms) if ms > 0 => ms,
                _ => {
                    return Err(format!(
                        "TPT_PROOF_TIMEOUT_MS must be a positive whole number of milliseconds, got `{text}`"
                    ))
                }
            };
        }
        Ok(config)
    }
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            z3: PathBuf::from("z3"),
            timeout_ms: 10_000,
        }
    }
}

/// Encodes the VC, runs Z3 on it, and interprets the answer.
///
/// Encoding errors are reported as [`Outcome::Error`] and the solver is never run.
pub fn check(vc: &Vc, config: &SolverConfig) -> Outcome {
    let script = match encode(vc) {
        Ok(script) => script,
        Err(err) => return Outcome::Error(err.to_string()),
    };
    match run_solver(&script, config) {
        Ok(stdout) => parse_output(&stdout),
        Err(outcome) => outcome,
    }
}

/// Like [`check`], but the solver is asked for a proof and the kernel checks it.
///
/// The answer is [`Outcome::Verified`] only when the kernel accepts the proof
/// of the VC. If the solver says `unsat` but the proof cannot be checked, the
/// answer is [`Outcome::Unchecked`] with the reason. A counterexample is found
/// by [`check`], because proofs do not come with models.
pub fn verify(vc: &Vc, config: &SolverConfig) -> Outcome {
    let script = match encode_with_proof(vc) {
        Ok(script) => script,
        Err(err) => return Outcome::Error(err.to_string()),
    };
    let stdout = match run_solver(&script, config) {
        Ok(stdout) => stdout,
        Err(outcome) => return outcome,
    };
    match stdout.lines().next().unwrap_or("").trim() {
        "unsat" => match reflect::reconstruct(vc, &stdout) {
            Ok(_) => Outcome::Verified,
            Err(err) => Outcome::Unchecked {
                reason: err.to_string(),
            },
        },
        "sat" => check(vc, config),
        _ => parse_output(&stdout),
    }
}

/// Extra time past the solver's own timeout before the process is killed. `-t:`
/// bounds Z3's search, not its startup or a loop that never checks the clock.
const KILL_GRACE: Duration = Duration::from_secs(5);

/// How often the driver checks whether the solver has exited.
const POLL: Duration = Duration::from_millis(5);

/// Runs the solver on `script` and returns its standard output. A solver that
/// runs past its timeout plus [`KILL_GRACE`] is killed and reported as
/// [`Outcome::Timeout`]. Any other failure to run it is an [`Outcome::Error`].
fn run_solver(script: &str, config: &SolverConfig) -> Result<String, Outcome> {
    let mut child = Command::new(&config.z3)
        .arg("-in")
        .arg(format!("-t:{}", config.timeout_ms))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|err| {
            Outcome::Error(format!("could not start `{}`: {err}", config.z3.display()))
        })?;

    // The pipes are served by their own threads, so that a solver which stops
    // reading or writing cannot block the driver.
    let stdin = child.stdin.take();
    let script = script.to_string();
    let writer = thread::spawn(move || match stdin {
        Some(mut stdin) => stdin.write_all(script.as_bytes()),
        None => Ok(()),
    });
    let stdout = child.stdout.take();
    let reader = thread::spawn(move || {
        let mut text = String::new();
        match stdout {
            Some(mut stdout) => stdout.read_to_string(&mut text).map(|_| text),
            None => Ok(text),
        }
    });

    let deadline = Instant::now() + Duration::from_millis(config.timeout_ms) + KILL_GRACE;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) if Instant::now() < deadline => thread::sleep(POLL),
            Ok(None) => {
                // Killing the process closes its pipes, which ends both threads.
                let _ = child.kill();
                let _ = child.wait();
                return Err(Outcome::Timeout);
            }
            Err(err) => {
                let _ = child.kill();
                return Err(Outcome::Error(format!("z3 failed: {err}")));
            }
        }
    }

    match writer.join() {
        Ok(Ok(())) => {}
        Ok(Err(err)) => {
            return Err(Outcome::Error(format!(
                "could not send the script to z3: {err}"
            )))
        }
        Err(_) => return Err(Outcome::Error("the script writer panicked".to_string())),
    }
    match reader.join() {
        Ok(Ok(text)) => Ok(text),
        Ok(Err(err)) => Err(Outcome::Error(format!("z3 failed: {err}"))),
        Err(_) => Err(Outcome::Error("the output reader panicked".to_string())),
    }
}

/// Interprets Z3's output for a script produced by [`encode`].
pub fn parse_output(stdout: &str) -> Outcome {
    let mut lines = stdout.lines();
    let verdict = lines.next().unwrap_or("").trim();
    let rest: String = lines.collect::<Vec<_>>().join("\n");
    match verdict {
        "unsat" => Outcome::SolverUnsat,
        "sat" => Outcome::Failed {
            counterexample: rest.trim().to_string(),
        },
        "unknown" if rest.contains("timeout") => Outcome::Timeout,
        "unknown" => Outcome::Unknown(rest.trim().to_string()),
        other => Outcome::Error(format!("unexpected solver output: `{other}`")),
    }
}

#[cfg(test)]
#[path = "../../../tests-support/tools.rs"]
mod test_tools;

#[cfg(test)]
mod tests {
    use super::test_tools as tools;
    use super::*;
    use std::fs;
    use std::path::Path;

    fn int(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn ok_vc() -> Vc {
        // Under x >= 0, x + 1 > 0.
        Vc {
            name: "increment is positive".to_string(),
            vars: vec![("x".to_string(), Sort::Int)],
            assumptions: vec![Expr::Le(Box::new(Expr::Int(0)), Box::new(int("x")))],
            goal: Expr::Lt(
                Box::new(Expr::Int(0)),
                Box::new(Expr::Add(Box::new(int("x")), Box::new(Expr::Int(1)))),
            ),
        }
    }

    #[test]
    fn encodes_a_valid_vc() {
        let script = encode(&ok_vc()).expect("encodes");
        assert_eq!(
            script,
            "(set-logic ALL)\n\
             (declare-const x Int)\n\
             (assert (<= 0 x))\n\
             (assert (not (< 0 (+ x 1))))\n\
             (check-sat)\n\
             (get-model)\n"
        );
    }

    #[test]
    fn negative_literals_are_wrapped() {
        let vc = Vc {
            name: "neg".to_string(),
            vars: vec![],
            assumptions: vec![],
            goal: Expr::Eq(Box::new(Expr::Int(-3)), Box::new(Expr::Int(-3))),
        };
        assert!(encode(&vc).expect("encodes").contains("(= (- 3) (- 3))"));
    }

    #[test]
    fn undeclared_variables_are_rejected() {
        let mut vc = ok_vc();
        vc.vars.clear();
        assert_eq!(
            encode(&vc),
            Err(EncodeError::UndeclaredVariable("x".to_string()))
        );
    }

    #[test]
    fn sort_errors_are_rejected_before_the_solver() {
        let vc = Vc {
            name: "bad".to_string(),
            vars: vec![("b".to_string(), Sort::Bool)],
            assumptions: vec![],
            goal: Expr::Lt(Box::new(int("b")), Box::new(Expr::Int(1))),
        };
        assert_eq!(
            encode(&vc),
            Err(EncodeError::SortMismatch {
                expected: Sort::Int,
                found: Sort::Bool,
            })
        );
    }

    #[test]
    fn invalid_names_are_rejected() {
        let mut vc = ok_vc();
        vc.vars = vec![("x y".to_string(), Sort::Int)];
        assert!(matches!(encode(&vc), Err(EncodeError::InvalidName(_))));
    }

    #[test]
    fn parses_unsat_as_solver_unsat_not_verified() {
        assert_eq!(parse_output("unsat\n"), Outcome::SolverUnsat);
    }

    #[test]
    fn parses_sat_with_model() {
        let outcome = parse_output("sat\n(model\n  (define-fun x () Int (- 1))\n)\n");
        match outcome {
            Outcome::Failed { counterexample } => assert!(counterexample.contains("define-fun x")),
            other => panic!("expected Failed, got {other:?}"),
        }
    }

    #[test]
    fn parses_timeout_and_unknown() {
        assert_eq!(
            parse_output("unknown\n(incomplete (theory timeout))\n"),
            Outcome::Timeout
        );
        assert!(matches!(
            parse_output("unknown\n(incomplete quantifiers)\n"),
            Outcome::Unknown(_)
        ));
    }

    #[test]
    fn rejects_unexpected_output() {
        assert!(matches!(parse_output("garbage"), Outcome::Error(_)));
    }

    #[test]
    fn config_comes_from_the_named_variables() {
        let values = |name: &str| match name {
            "TPT_PROOF_Z3" => Some("C:/tools/z3.exe".to_string()),
            "TPT_PROOF_TIMEOUT_MS" => Some(" 2500 ".to_string()),
            _ => None,
        };
        let config = SolverConfig::from_lookup(values).expect("valid values");
        assert_eq!(config.z3, PathBuf::from("C:/tools/z3.exe"));
        assert_eq!(config.timeout_ms, 2500);
    }

    #[test]
    fn unset_variables_keep_the_defaults() {
        let config = SolverConfig::from_lookup(|_| None).expect("no values is valid");
        let default = SolverConfig::default();
        assert_eq!(config.z3, default.z3);
        assert_eq!(config.timeout_ms, default.timeout_ms);
    }

    #[test]
    fn a_bad_timeout_is_rejected_with_its_text() {
        for text in ["soon", "0", "-5", "1.5"] {
            let lookup = |name: &str| (name == "TPT_PROOF_TIMEOUT_MS").then(|| text.to_string());
            let error = SolverConfig::from_lookup(lookup).expect_err("not a positive whole number");
            assert!(error.contains(text), "{error}");
        }
    }

    #[test]
    fn missing_solver_is_an_error_not_a_proof() {
        let config = SolverConfig {
            z3: PathBuf::from("definitely-not-a-real-z3-binary"),
            timeout_ms: 1_000,
        };
        assert!(matches!(check(&ok_vc(), &config), Outcome::Error(_)));
    }

    /// A stand-in solver that sleeps and never answers. Its arguments are ignored.
    fn hanging_solver(dir: &Path) -> PathBuf {
        #[cfg(windows)]
        let (name, body) = ("hang.cmd", "@echo off\r\nping -n 30 127.0.0.1 > nul\r\n");
        #[cfg(not(windows))]
        let (name, body) = ("hang.sh", "#!/bin/sh\nsleep 30\n");
        let path = dir.join(name);
        fs::write(&path, body).expect("the test directory is writable");
        #[cfg(not(windows))]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755))
                .expect("the test script can be made executable");
        }
        path
    }

    #[test]
    fn a_solver_that_hangs_is_killed_and_reported_as_a_timeout() {
        let dir = std::env::temp_dir().join(format!("tpt-proof-hang-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("the temp directory is writable");
        let config = SolverConfig {
            z3: hanging_solver(&dir),
            timeout_ms: 100,
        };
        let started = Instant::now();
        let outcome = check(&ok_vc(), &config);
        assert_eq!(outcome, Outcome::Timeout, "got {outcome:?}");
        assert!(
            started.elapsed() < Duration::from_secs(20),
            "the hung solver was not killed in time"
        );
    }

    /// Needs a `z3` binary on the PATH. Run with `cargo test -- --ignored`.
    #[test]
    fn z3_proves_the_valid_vc() {
        if tools::skip_unless("z3") {
            return;
        }
        let outcome = check(&ok_vc(), &SolverConfig::default());
        assert_eq!(outcome, Outcome::SolverUnsat, "got {outcome:?}");
    }

    /// Needs a `z3` binary on the PATH. Run with `cargo test -- --ignored`.
    #[test]
    fn z3_finds_a_counterexample_to_a_false_vc() {
        if tools::skip_unless("z3") {
            return;
        }
        let mut vc = ok_vc();
        // Drop the assumption, so x = -1 is a counterexample.
        vc.assumptions.clear();
        match check(&vc, &SolverConfig::default()) {
            Outcome::Failed { counterexample } => assert!(counterexample.contains("x")),
            other => panic!("expected a counterexample, got {other:?}"),
        }
    }
}

/// A parsed solver term: an atom or a parenthesised list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

pub(crate) fn parse_sexps(text: &str) -> Vec<Sexp> {
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    let mut atom = String::new();
    let flush = |atom: &mut String, stack: &mut Vec<Vec<Sexp>>| {
        if !atom.is_empty() {
            if let Some(top) = stack.last_mut() {
                top.push(Sexp::Atom(std::mem::take(atom)));
            }
        }
    };
    for c in text.chars() {
        match c {
            '(' => {
                flush(&mut atom, &mut stack);
                stack.push(Vec::new());
            }
            ')' => {
                flush(&mut atom, &mut stack);
                if stack.len() > 1 {
                    let list = stack.pop().unwrap_or_default();
                    if let Some(top) = stack.last_mut() {
                        top.push(Sexp::List(list));
                    }
                }
            }
            c if c.is_whitespace() => flush(&mut atom, &mut stack),
            c => atom.push(c),
        }
    }
    flush(&mut atom, &mut stack);
    stack.into_iter().next().unwrap_or_default()
}

/// Renders a model value as the solver's integer or boolean text, without the
/// `(- n)` wrapper that the solver uses for negative numbers.
fn render_value(value: &Sexp) -> String {
    match value {
        Sexp::Atom(atom) => atom.clone(),
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(op), Sexp::Atom(n)] if op == "-" => format!("-{n}"),
            _ => format!("{items:?}"),
        },
    }
}

fn collect_definitions(sexps: &[Sexp], out: &mut Vec<(String, String)>) {
    for sexp in sexps {
        if let Sexp::List(items) = sexp {
            match items.as_slice() {
                [Sexp::Atom(head), Sexp::Atom(name), _, _, value] if head == "define-fun" => {
                    out.push((name.clone(), render_value(value)));
                }
                _ => collect_definitions(items, out),
            }
        }
    }
}

/// The variable values in a counterexample: `(name, value)` pairs in the order the
/// solver reports them. Values are integers or `true` and `false`.
pub fn counterexample_values(counterexample: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    collect_definitions(&parse_sexps(counterexample), &mut out);
    out
}

#[cfg(test)]
mod model_tests {
    use super::*;

    #[test]
    fn reads_integer_and_negative_values() {
        let model =
            "(\n  (define-fun _2 () Int\n    (- 7))\n  (define-fun _1 () Int\n    255)\n)\n";
        assert_eq!(
            counterexample_values(model),
            vec![
                ("_2".to_string(), "-7".to_string()),
                ("_1".to_string(), "255".to_string()),
            ]
        );
    }

    #[test]
    fn reads_boolean_values() {
        let model = "(\n  (define-fun flag () Bool\n    false)\n)";
        assert_eq!(
            counterexample_values(model),
            vec![("flag".to_string(), "false".to_string())]
        );
    }

    #[test]
    fn an_empty_or_unrelated_model_has_no_values() {
        assert!(counterexample_values("").is_empty());
        assert!(counterexample_values("(error \"oops\")").is_empty());
    }
}
