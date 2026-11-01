#[doc = "tpt-proof-invariant: 5: total == i + 1"]
pub fn count_wrong(n: u32) -> u32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        total += 1;
        i += 1;
    }
    total
}
