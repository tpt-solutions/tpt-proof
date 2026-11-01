#[doc = "tpt-proof-requires: x == -7 && y == -2"]
#[doc = "tpt-proof-ensures: |result| *result == 4"]
pub fn div_euclid_claim(x: i32, y: i32) -> i32 {
    if y != 0 { x / y } else { 0 }
}
