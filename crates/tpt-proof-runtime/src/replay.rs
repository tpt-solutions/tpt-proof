//! Counterexample replay (spec.txt §7, phase 5).
//!
//! When the static verifier reports a counterexample, the values it found can be
//! fed back to the real function. [`run`] calls the function under those values
//! and reports whether a contract failed, which confirms the counterexample on
//! the actual code rather than the model of it.
//!
//! Contracts are debug assertions, so a replay in a release build finds no
//! failure. [`Replay::Passed`] means only that the failure did not reproduce in
//! this build.

use std::any::Any;
use std::panic::{catch_unwind, UnwindSafe};

/// The messages the contract macros and [`crate::runtime_check!`] panic with.
const CONTRACT_FAILURES: [&str; 3] = [
    "precondition failed",
    "postcondition failed",
    "runtime check failed",
];

/// The outcome of replaying one input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Replay {
    /// The function ran without panicking.
    Passed,
    /// A contract failed. The message is the contract's own message.
    Confirmed(String),
    /// The function panicked for another reason, such as an index out of bounds.
    /// The verifier's counterexample is still a real failure of the code.
    Panicked(String),
}

/// Calls `f` and reports how it finished. Any panic is caught, so the caller
/// can run many replays in one test. The panic message is still printed by the
/// default panic hook.
pub fn run<F: FnOnce() + UnwindSafe>(f: F) -> Replay {
    match catch_unwind(f) {
        Ok(()) => Replay::Passed,
        Err(payload) => {
            let message = message(payload.as_ref());
            if CONTRACT_FAILURES.iter().any(|kind| message.contains(kind)) {
                Replay::Confirmed(message)
            } else {
                Replay::Panicked(message)
            }
        }
    }
}

fn message(payload: &(dyn Any + Send)) -> String {
    if let Some(text) = payload.downcast_ref::<&str>() {
        (*text).to_string()
    } else if let Some(text) = payload.downcast_ref::<String>() {
        text.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_function_that_returns_is_passed() {
        assert_eq!(run(|| {}), Replay::Passed);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn a_failing_runtime_check_is_confirmed() {
        let x = 0;
        let outcome = run(move || crate::runtime_check!(x > 0));
        assert!(
            matches!(outcome, Replay::Confirmed(ref m) if m.contains("x > 0")),
            "{outcome:?}"
        );
    }

    #[test]
    fn other_panics_are_reported_as_panicked() {
        let outcome = run(|| {
            let values: Vec<u8> = Vec::new();
            let _ = values[3];
        });
        assert!(matches!(outcome, Replay::Panicked(_)), "{outcome:?}");
    }
}
