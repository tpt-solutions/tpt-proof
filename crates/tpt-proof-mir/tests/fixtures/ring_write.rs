// A write into a four-slot ring buffer at a position taken modulo the length.
// The index is always in bounds, whatever the head is.
pub fn write(buffer: [u8; 4], head: usize, value: u8) -> [u8; 4] {
    let mut next = buffer;
    next[head % 4] = value;
    next
}
