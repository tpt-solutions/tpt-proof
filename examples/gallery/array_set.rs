// Writing an element, then reading it back. After the write, reading the same
// index returns the value written.
#[doc = "tpt-proof-requires: i < 4"]
#[doc = "tpt-proof-ensures: |result| *result == v"]
pub fn set_then_get(mut a: [u8; 4], i: usize, v: u8) -> u8 {
    a[i] = v;
    a[i]
}
