// The same function without `lo <= hi`. The postcondition fails when lo > hi.
#[doc = "tpt-proof-ensures: |result| *result >= lo && *result <= hi"]
pub fn clamp(value: u32, lo: u32, hi: u32) -> u32 {
    if value < lo {
        lo
    } else if value > hi {
        hi
    } else {
        value
    }
}
