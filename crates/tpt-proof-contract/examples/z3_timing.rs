//! Times Z3 on the verification conditions for a few workloads.
//!
//! Run with `cargo run -p tpt-proof-contract --release --example z3_timing`.
//! Needs a `z3` binary on the PATH. Each VC is checked `RUNS` times and the
//! median wall-clock time of the solver call is printed.

use std::time::{Duration, Instant};

use tpt_proof_contract::smt::{check, SolverConfig};
use tpt_proof_contract::vc::{Expr, Sort, Vc};
use tpt_proof_contract::wp::{generate, Function, Stmt};
use tpt_proof_contract::Outcome;

const RUNS: usize = 5;

fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
}

fn int_lit(n: i64) -> Expr {
    Expr::Int(n)
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}

fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Sub(Box::new(a), Box::new(b))
}

fn lt(a: Expr, b: Expr) -> Expr {
    Expr::Lt(Box::new(a), Box::new(b))
}

fn le(a: Expr, b: Expr) -> Expr {
    Expr::Le(Box::new(a), Box::new(b))
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}

fn assign(name: &str, value: Expr) -> Stmt {
    Stmt::Assign {
        var: name.to_string(),
        value,
    }
}

/// Counts `i` up to `n` with a loop, then checks `x == n`.
fn count_to_n() -> Function {
    let invariant = Expr::And(vec![
        le(int_lit(0), var("i")),
        le(var("i"), var("n")),
        eq(var("x"), var("i")),
    ]);
    Function {
        name: "count_to_n".to_string(),
        vars: vec![
            ("n".to_string(), Sort::Int),
            ("i".to_string(), Sort::Int),
            ("x".to_string(), Sort::Int),
        ],
        requires: vec![le(int_lit(0), var("n"))],
        ranges: vec![],
        body: vec![
            assign("i", int_lit(0)),
            assign("x", int_lit(0)),
            Stmt::While {
                cond: lt(var("i"), var("n")),
                invariant,
                body: vec![
                    assign("x", add(var("x"), int_lit(1))),
                    assign("i", add(var("i"), int_lit(1))),
                ],
            },
        ],
        ensures: vec![eq(var("x"), var("n"))],
    }
}

/// Absolute value with a branch.
fn abs() -> Function {
    Function {
        name: "abs".to_string(),
        vars: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        requires: vec![],
        ranges: vec![],
        body: vec![Stmt::If {
            cond: lt(var("x"), int_lit(0)),
            then_branch: vec![assign("y", sub(int_lit(0), var("x")))],
            else_branch: vec![assign("y", var("x"))],
        }],
        ensures: vec![le(int_lit(0), var("y"))],
    }
}

/// A straight-line chain of `steps` increments, checked against the total.
fn chain(steps: usize) -> Function {
    let mut vars = vec![("x".to_string(), Sort::Int)];
    let mut body = Vec::new();
    for i in 0..steps {
        let name = format!("v{i}");
        let previous = if i == 0 {
            var("x")
        } else {
            var(&format!("v{}", i - 1))
        };
        vars.push((name.clone(), Sort::Int));
        body.push(assign(&name, add(previous, int_lit(1))));
    }
    let last = format!("v{}", steps - 1);
    Function {
        name: format!("chain_{steps}"),
        vars,
        requires: vec![le(int_lit(0), var("x"))],
        ranges: vec![],
        body,
        ensures: vec![eq(var(&last), add(var("x"), int_lit(steps as i64)))],
    }
}

fn median(mut times: Vec<Duration>) -> Duration {
    times.sort();
    times[times.len() / 2]
}

fn time_vc(label: &str, vc: &Vc, config: &SolverConfig) {
    let mut times = Vec::with_capacity(RUNS);
    let mut last = Outcome::Timeout;
    for _ in 0..RUNS {
        let start = Instant::now();
        last = check(vc, config);
        times.push(start.elapsed());
    }
    println!(
        "{label:<28} {:>10.1} ms  {:?}",
        median(times).as_secs_f64() * 1e3,
        last
    );
}

fn main() {
    let config = SolverConfig::default();
    println!("{:<28} {:>13}  outcome", "vc", "median");

    let cases = [
        ("loop: count_to_n", generate(&count_to_n())),
        ("branch: abs", generate(&abs())),
        ("chain: 10 steps", generate(&chain(10))),
        ("chain: 100 steps", generate(&chain(100))),
        ("chain: 1000 steps", generate(&chain(1000))),
    ];
    for (label, vcs) in cases {
        let vcs = vcs.expect("workload generates");
        for vc in &vcs {
            time_vc(label, vc, &config);
        }
    }
}
