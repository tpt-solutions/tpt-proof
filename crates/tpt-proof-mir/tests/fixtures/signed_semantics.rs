#[doc = "tpt-proof-requires: x == -7 && y == -2"]
#[doc = "tpt-proof-ensures: |result| *result == 3"]
pub fn div_case(x: i32, y: i32) -> i32 {
    if y != 0 { x / y } else { 0 }
}

#[doc = "tpt-proof-requires: x == -7 && y == 2"]
#[doc = "tpt-proof-ensures: |result| *result == -1"]
pub fn rem_case(x: i32, y: i32) -> i32 {
    if y != 0 { x % y } else { 0 }
}
