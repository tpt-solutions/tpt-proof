#[doc = "tpt-proof-requires: x < 100"]
#[doc = "tpt-proof-ensures: |result| *result >= 100"]
pub fn plus100(x: u8) -> u8 {
    x + 100
}
