// A loop with an invariant. The invariant must hold on entry, be preserved by
// each iteration, and imply the postcondition when the loop exits.
#[doc = "tpt-proof-invariant: 8: i <= n && total == i"]
#[doc = "tpt-proof-ensures: |result| *result == n"]
pub fn count_up(n: u32) -> u32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        total += 1;
        i += 1;
    }
    total
}
