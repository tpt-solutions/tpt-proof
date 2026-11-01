//! Tests for the Layer 1 derive attributes, `#[refined]` and `#[state_machine]`.

use std::marker::PhantomData;
use tpt_proof::prelude::*;

#[refined(value < total)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Block {
    value: usize,
    total: usize,
}

#[refined(value < 8)]
#[derive(Debug)]
struct Slot {
    value: u8,
}

#[state_machine(Idle, Busy)]
#[derive(Debug)]
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

    fn begin(self) -> Worker<Busy> {
        self.transition()
    }
}

impl Worker<Busy> {
    fn finish(self) -> Worker<Idle> {
        self.transition()
    }
}

impl<S: WorkerState> Worker<S> {
    fn id(&self) -> u32 {
        self.id
    }
}

#[test]
fn refined_constructor_checks_a_field_bound() {
    assert_eq!(Block::new(3, 4).map(|block| block.value()), Some(3));
    assert!(Block::new(4, 4).is_none());
}

#[test]
fn refined_constructor_checks_a_literal_bound() {
    assert_eq!(Slot::new(7).map(|slot| slot.value()), Some(7));
    assert!(Slot::new(8).is_none());
}

#[test]
fn transitions_keep_the_fields() {
    let worker = Worker::start(9).begin().finish();
    assert_eq!(worker.id(), 9);
    assert!(format!("{worker:?}").contains("id: 9"));
}
