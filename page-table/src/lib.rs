// #![feature(nonnull_slice_from_raw_parts)]
#![cfg_attr(feature="linuxmodule", no_std)]
#[cfg(not(feature="linuxmodule"))]
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

// #[repr(C)]
// pub struct MapFlags {
//     writable: u64,
//     readable: u64,
//     executable: u64,
//     devicemem: u64,
//     usermode: u64,
//     bar: u64,
// }

pub const WRITABLE: u64 = 1 << 0;
pub const READABLE: u64 = 1 << 1;
pub const EXECUTABLE: u64 = 1 << 2;
pub const DEVICEMEM: u64 = 1 << 3;
pub const USERMODE: u64 = 1 << 4;
pub const BAR: u64 = 1 << 5;

#[no_mangle]
pub extern "C" fn v_x8664pml4_map(
    pt_ptr: *mut core::ffi::c_void,
    vaddr: u64,
    sz: u64,
    flags: u64) -> i64
{
    assert!(sz == 4096);
    0
}