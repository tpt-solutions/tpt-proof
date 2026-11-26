// Binary search over a four-element array. The contents are not part of the
// contract, which only speaks about indices: the result is at most 4, and every
// read `a[mid]` is in bounds because lo <= mid < hi <= 4.
#[doc = "tpt-proof-invariant: 9: lo <= hi && hi <= 4"]
#[doc = "tpt-proof-ensures: |result| *result <= 4"]
pub fn search(a: [u8; 4], key: u8) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = 4;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] < key {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}
