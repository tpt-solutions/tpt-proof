#[doc = "tpt-proof-requires: d < 100"]
pub fn bump(d: u8) -> u8 {
    d + 1
}

pub fn careless(x: u8) -> u8 {
    bump(x)
}
