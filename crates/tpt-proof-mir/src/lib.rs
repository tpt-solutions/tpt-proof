//! MIR access and translation for tpt-proof (spec.txt §5).
//!
//! [`translate::translate`] turns the optimized MIR of a function into
//! verification conditions for the subset it supports. The `tpt-proof-mir`
//! binary runs the compiler front end and checks each VC with Z3.

#![feature(rustc_private)]
#![forbid(unsafe_code)]

extern crate rustc_attr_ir;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_span;

pub mod translate;
