//! Type-state: a handle's state is part of its type, so invalid transitions do
//! not compile.
//!
//! This is the hand-written form of `#[state_machine(Open, Writing, Closed)]`
//! from SPEC.md §3. The `State` trait is sealed, so outside code cannot add
//! states the transitions were not written for.
//!
//! ```
//! use tpt_proof_core::state_machine::{FileHandle, Open};
//!
//! let handle: FileHandle<Open> = FileHandle::open(7);
//! let writing = handle.begin_write();
//! let open_again = writing.end_write();
//! let _closed = open_again.close();
//! ```
//!
//! Writing to a closed handle does not compile:
//!
//! ```compile_fail
//! use tpt_proof_core::state_machine::{FileHandle, Open};
//!
//! let closed = FileHandle::<Open>::open(7).close();
//! let _ = closed.begin_write();
//! ```

mod sealed {
    pub trait Sealed {}
}

/// A state a [`FileHandle`] can be in. The trait is sealed.
pub trait State: sealed::Sealed {}

/// The handle is open and idle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Open;

/// The handle is in the middle of a write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Writing;

/// The handle is closed and can no longer be used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Closed;

impl sealed::Sealed for Open {}
impl sealed::Sealed for Writing {}
impl sealed::Sealed for Closed {}
impl State for Open {}
impl State for Writing {}
impl State for Closed {}

/// A file handle whose state is `S`. Each transition consumes the handle and
/// returns it in the new state.
#[derive(Debug)]
pub struct FileHandle<S: State> {
    fd: u32,
    state: std::marker::PhantomData<S>,
}

impl FileHandle<Open> {
    /// Opens a handle on the given descriptor.
    pub fn open(fd: u32) -> Self {
        FileHandle {
            fd,
            state: std::marker::PhantomData,
        }
    }

    /// Starts a write. Consumes the open handle.
    pub fn begin_write(self) -> FileHandle<Writing> {
        FileHandle {
            fd: self.fd,
            state: std::marker::PhantomData,
        }
    }

    /// Closes the handle.
    pub fn close(self) -> FileHandle<Closed> {
        FileHandle {
            fd: self.fd,
            state: std::marker::PhantomData,
        }
    }
}

impl FileHandle<Writing> {
    /// Finishes a write and returns the handle to the open state.
    pub fn end_write(self) -> FileHandle<Open> {
        FileHandle {
            fd: self.fd,
            state: std::marker::PhantomData,
        }
    }
}

impl<S: State> FileHandle<S> {
    /// The descriptor. Available in every state.
    pub fn fd(&self) -> u32 {
        self.fd
    }
}
