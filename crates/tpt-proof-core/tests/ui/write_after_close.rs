use tpt_proof_core::state_machine::FileHandle;

fn main() {
    let closed = FileHandle::open(7).close();
    let _ = closed.begin_write();
}
