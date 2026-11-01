//! Layer 4 of tpt-proof: runtime verification (spec.txt §3).
//!
//! [`runtime_check!`] turns a specification into a debug assertion. It is
//! active in debug builds and compiles to nothing in release builds, so it adds
//! no runtime cost to a shipped binary. It is the tool for code that cannot be
//! verified statically: FFI, legacy code, and third-party libraries.
//!
//! The attribute form, `#[runtime_check(...)]`, needs a proc-macro crate and is
//! not built yet.

#![forbid(unsafe_code)]

/// Checks a condition in debug builds. In release builds it compiles to nothing.
///
/// ```
/// let xs = [1, 2, 3];
/// tpt_proof_runtime::runtime_check!(xs.len() == 3);
/// tpt_proof_runtime::runtime_check!(xs[0] < xs[1], "xs must be sorted at {}", 0);
/// ```
#[macro_export]
macro_rules! runtime_check {
    ($cond:expr $(,)?) => {
        debug_assert!($cond, "runtime check failed: {}", stringify!($cond))
    };
    ($cond:expr, $($arg:tt)+) => {
        debug_assert!($cond, $($arg)+)
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn passing_check_does_nothing() {
        crate::runtime_check!(1 + 1 == 2);
        crate::runtime_check!(true, "message is ignored when the check passes");
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "runtime check failed: 1 == 2")]
    fn failing_check_panics_in_debug_builds() {
        crate::runtime_check!(1 == 2);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "index 4 is bad")]
    fn custom_message_is_used() {
        crate::runtime_check!(false, "index {} is bad", 4);
    }
}
