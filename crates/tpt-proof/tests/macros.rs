//! Tests for the contract attributes. Checks are `debug_assert!`s, so the
//! failure tests only run in debug builds.

use tpt_proof::prelude::*;

#[requires(divisor != 0)]
fn divide(value: u32, divisor: u32) -> u32 {
    value / divisor
}

#[ensures(|result| *result >= 0)]
fn abs(x: i32) -> i32 {
    if x < 0 {
        -x
    } else {
        x
    }
}

#[ensures(|result| match result {
    Ok(n) => *n >= 0,
    Err(_) => true,
})]
fn parse_positive(text: &str) -> Result<i32, std::num::ParseIntError> {
    let n = text.parse::<i32>()?;
    if n < 0 {
        return Ok(0);
    }
    Ok(n)
}

struct Counter {
    n: u32,
}

impl Counter {
    #[runtime_check(self.n < 10)]
    fn bump(&mut self) {
        self.n += 1;
    }
}

#[requires(lo <= hi)]
#[requires(hi < 100)]
fn span(lo: u32, hi: u32) -> u32 {
    hi - lo
}

#[test]
fn passing_contracts_do_not_change_results() {
    assert_eq!(divide(10, 2), 5);
    assert_eq!(abs(-3), 3);
    assert_eq!(parse_positive("7").unwrap(), 7);
    assert_eq!(parse_positive("-7").unwrap(), 0);
    assert!(parse_positive("x").is_err());
    assert_eq!(span(2, 9), 7);
    let mut counter = Counter { n: 0 };
    counter.bump();
    assert_eq!(counter.n, 1);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "precondition failed")]
fn failing_precondition_panics_in_debug() {
    divide(1, 0);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "precondition failed")]
fn second_of_two_requires_is_checked() {
    span(5, 200);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "postcondition failed")]
fn failing_postcondition_panics_in_debug() {
    // The body returns the wrong sign, so the postcondition fails.
    #[ensures(|result| *result >= 0)]
    fn wrong_sign(x: i32) -> i32 {
        -x.abs()
    }
    wrong_sign(3);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "runtime check failed")]
fn failing_runtime_check_on_a_method_panics_in_debug() {
    let mut counter = Counter { n: 10 };
    counter.bump();
}
