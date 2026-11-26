// Reading an element of a fixed-size array. The index must be in bounds, and
// the precondition says so. The verifier checks the bounds check at the read.
#[doc = "tpt-proof-requires: i < 4"]
pub fn get(a: [u8; 4], i: usize) -> u8 {
    a[i]
}
