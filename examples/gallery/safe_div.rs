// Division is safe only when the divisor is non-zero. The precondition says so,
// and the verifier checks the division at its call site, not here.
#[doc = "tpt-proof-requires: y != 0"]
#[doc = "tpt-proof-ensures: |result| *result <= x"]
pub fn quotient(x: u32, y: u32) -> u32 {
    x / y
}
