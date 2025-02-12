#![no_std]
// #![feature(nonnull_slice_from_raw_parts)]

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


pub extern "C" fn v_x8664pml4_init(pt_ptr: *mut core::ffi::c_void) -> i64 {
    0 // return the PML4 state representation of the verified implementation.
}


#[no_mangle]
pub extern "C" fn v_x8664pml4_map(
    pt_ptr: *mut core::ffi::c_void,
    vaddr: u64,
    sz: u64,
    flags: u64) -> i64
{
    // assert!(sz == 4096);
    0 // return 0 to indicate success
}




#[no_mangle]
pub extern "C" fn v_x8664pml4_unmap(
    pt_ptr: *mut core::ffi::c_void,
    vaddr: u64,
    sz: u64) -> i64
{
    // assert!(sz == 4096);
    0 // return 0 to indicate success
}


#[no_mangle]
pub extern "C" fn v_x8664pml4_protect(
    pt_ptr: *mut core::ffi::c_void,
    vaddr: u64,
    sz: u64,
    flags: u64) -> i64
{
    // assert!(sz == 4096);
    0 // return 0 to indicate success
}

