// #![feature(nonnull_slice_from_raw_parts)]
//#![no_std]
#![cfg_attr(feature="linuxmodule", no_std)]
#[cfg(not(feature="linuxmodule"))]
extern crate alloc;

pub mod impl_u;
pub mod definitions_u;
pub mod spec_t;
pub mod extra;
pub mod theorem;

use vstd::prelude::verus;
// #[cfg(feature="linuxmodule")]
use vstd::prelude::Tracked;
// #[cfg(feature="linuxmodule")]
use crate::spec_t::mmu::defs::{ PageTableEntryExec, MemRegionExec };
// #[cfg(feature="linuxmodule")]
use crate::spec_t::os_code_vc::{ Prophecy, Token, CodeVC };
verus!{

global size_of usize == 8;


#[cfg(feature="linuxmodule")]
use core::panic::PanicInfo;

/// This function is called on panic.
#[panic_handler]
#[cfg(feature="linuxmodule")]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

#[cfg(feature="hlspec_user")]
pub mod hlspec_user;
//pub mod os_trace;

#[cfg(feature="linuxmodule")]
#[no_mangle]
pub extern "C" fn veros_init() -> i64 {
    0 // return 0 to indicate success
}

/// Entry point from the linux kernel to map a region of memory
// #[cfg(feature="linuxmodule")]
// #[used(linker)]
#[verifier(external_body)]
#[no_mangle]
pub extern "C" fn veros_map_frame(
    pt_ptr: u64,
    vaddr: u64,
    pte: PageTableEntryExec) -> i64
{

    let pml4 = pt_ptr as usize;
    let token: Tracked<Token> = Tracked::assume_new();
    let proph_res = Tracked(Prophecy::new());

    let (res, _tok) = impl_u::verified_impl::PTImpl::sys_do_map(token, pml4, vaddr as usize, pte, proph_res);
    if res.is_ok() {
        return 0;
    } else {
        return -1;
    }
}



// #[cfg(feature="linuxmodule")]
// #[used(linker)]
#[verifier(external_body)]
#[no_mangle]
pub extern "C" fn veros_unmap_frame(
    pt_ptr: u64,
    vaddr: u64,
    ret_frame: &mut MemRegionExec) -> i64
{
    let pml4 = pt_ptr as usize;
    let token: Tracked<Token> = Tracked::assume_new();
    let proph_res = Tracked(Prophecy::new());

    let (res, _tok) = impl_u::verified_impl::PTImpl::sys_do_unmap(token, pml4, vaddr as usize, proph_res);
    match res {
        Ok(frame) => {
            *ret_frame = frame;
            return 0;
        }
        Err(_) => {
            return -1;
        }
    }
    //0 // return 0 to indicate success
}


} // verus!
