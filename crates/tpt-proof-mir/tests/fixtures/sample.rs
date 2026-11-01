pub fn straight(x: u32) -> u32 {
    x + 1
}

pub fn branch(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

pub fn looping(n: u32) -> u32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        total += i;
        i += 1;
    }
    total
}
