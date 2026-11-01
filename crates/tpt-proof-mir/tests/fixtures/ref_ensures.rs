#[doc = "tpt-proof-requires: *x < 100"]
#[doc = "tpt-proof-ensures: |result| *result == *x + 1"]
pub fn bump_checked(x: &u8) -> u8 {
    *x + 1
}
