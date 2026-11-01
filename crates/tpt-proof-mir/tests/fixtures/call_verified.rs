#[doc = "tpt-proof-requires: d < 100"]
#[doc = "tpt-proof-ensures: |result| *result >= d"]
pub fn bump(d: u8) -> u8 {
    d + 1
}

#[doc = "tpt-proof-requires: x < 50"]
#[doc = "tpt-proof-ensures: |result| *result >= x"]
pub fn caller(x: u8) -> u8 {
    bump(x)
}
