pub fn double_small(x: u8) -> u8 {
    if x < 128 { x * 2 } else { x }
}
