//! Property-based testing of contracts with proptest (spec.txt §3, phase 5).
//!
//! Enable the `proptest` feature. [`check`] generates inputs from a strategy and
//! asserts that a property holds for each. A failing input is shrunk by proptest
//! before it is reported.

use std::fmt::Debug;

use proptest::strategy::Strategy;
use proptest::test_runner::{Config, TestError, TestRunner};

/// Runs `property` on values from `strategy`. Panics with the smallest failing
/// value found if the property returns `false` or panics.
pub fn check<S, F>(strategy: S, property: F)
where
    S: Strategy,
    S::Value: Debug,
    F: Fn(&S::Value) -> bool,
{
    let mut runner = TestRunner::new(Config::default());
    let result = runner.run(&strategy, |value| {
        if property(&value) {
            Ok(())
        } else {
            Err(proptest::test_runner::TestCaseError::fail(format!(
                "property failed for {value:?}"
            )))
        }
    });
    if let Err(TestError::Fail(reason, value)) = result {
        panic!("property failed: {reason}; minimal input {value:?}");
    }
    if let Err(error) = result {
        panic!("property could not be checked: {error}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_true_property_passes() {
        check(0u32..1000, |n| n + 1 > *n);
    }

    #[test]
    #[should_panic(expected = "property failed")]
    fn a_false_property_fails_with_a_minimal_input() {
        check(0u32..1000, |n| *n < 10);
    }
}
