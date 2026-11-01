#[doc = "tpt-proof-ensures: |result| *result == x"]
pub fn read_back(x: u8) -> u8 {
    let r = &x;
    *r
}
