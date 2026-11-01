use std::marker::PhantomData;
use tpt_proof::prelude::*;

#[state_machine(Idle, Busy)]
struct Worker {
    id: u32,
}

impl Worker<Idle> {
    fn start(id: u32) -> Self {
        Worker {
            id,
            state: PhantomData,
        }
    }
}

impl Worker<Busy> {
    fn finish(self) -> Worker<Idle> {
        self.transition()
    }
}

fn main() {
    // `finish` exists only on `Worker<Busy>`, so this does not compile.
    let _ = Worker::start(1).finish();
}
