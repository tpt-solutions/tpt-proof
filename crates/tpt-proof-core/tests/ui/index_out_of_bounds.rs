use tpt_proof_core::refined::Index;

const BAD: Index<8> = Index::new_const(9);

fn main() {
    let _ = BAD;
}
