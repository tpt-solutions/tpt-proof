pub fn bump_small(x: u8) -> u8 {
    if x < 100 { x + 100 } else { x }
}
