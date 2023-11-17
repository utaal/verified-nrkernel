#![feature(nonnull_slice_from_raw_parts)]
extern crate alloc;

pub mod impl_u;
pub mod definitions_t;
pub mod definitions_u;
pub mod spec_t;
pub mod extra;

use vstd::prelude::verus;

verus!{

global size_of usize == 8;

}

fn main() {}
