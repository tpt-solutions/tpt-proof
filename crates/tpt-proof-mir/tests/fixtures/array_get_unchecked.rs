// The same read with no precondition: the verifier finds an index out of bounds.
pub fn get(a: [u8; 4], i: usize) -> u8 {
    a[i]
}
