#![feature(nonnull_slice_from_raw_parts)]
extern crate alloc;

pub mod impl_u;
pub mod definitions_t;
pub mod spec_t;

use vstd::prelude::verus;

verus!{

global size_of usize == 8;

}

fn main() {}
