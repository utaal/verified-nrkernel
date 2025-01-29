#![feature(nonnull_slice_from_raw_parts)]
extern crate alloc;

pub mod impl_u;
pub mod definitions_u;
pub mod spec_t;
pub mod extra;
pub mod theorem;

use vstd::prelude::verus;

verus!{

global size_of usize == 8;

}

//pub mod hlspec_user;
//pub mod os_trace;
