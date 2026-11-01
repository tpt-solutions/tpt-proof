#[doc = "tpt-proof-ensures: |result| *result <= x"]
pub fn quotient_guarded(x: u32, y: u32) -> u32 {
    if y != 0 { x / y } else { 0 }
}
