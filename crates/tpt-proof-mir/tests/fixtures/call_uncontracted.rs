pub fn opaque(x: u8) -> u8 {
    x
}

#[doc = "tpt-proof-ensures: |result| *result == x"]
pub fn caller_expects_more(x: u8) -> u8 {
    opaque(x)
}
