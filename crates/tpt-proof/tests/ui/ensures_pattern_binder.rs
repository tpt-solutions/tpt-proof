use tpt_proof::prelude::*;

#[ensures(|(a, b)| a > b)]
fn pair() -> (u32, u32) {
    (2, 1)
}

fn main() {}
