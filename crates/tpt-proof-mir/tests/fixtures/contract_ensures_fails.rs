#[doc = "tpt-proof-requires: x < 100"]
#[doc = "tpt-proof-ensures: |result| *result >= 150"]
pub fn plus100_loose(x: u8) -> u8 {
    x + 100
}
