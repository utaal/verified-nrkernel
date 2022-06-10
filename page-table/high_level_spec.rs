#[allow(unused_imports)] use crate::pervasive::*;
use seq::*;
use crate::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use state_machines_macros::*;
use map::*;

// RA: the ARMv8 architecture you can also load/store a pair of registers in one instruction,
//     (and I think even more than that)
//
//     now these are technically two loads/stores as I assume.  From the manual (C6.2.130 LDP):
//      data1 = Mem[address, dbytes, AccType_NORMAL];
//      data2 = Mem[address+dbytes, dbytes, AccType_NORMAL];
//      X[t] = data1;
//      X[t2] = data2;
//
//     the ARMv7 has a load multiple.
//
//     the other thing to consider here would be the SIMD registers, where we can do a
//     load/store of up to 512bits.
//
//     I think conceptually we could say that this will be just two load/stores. Though, the
//     difference here may be subtle, if you do two independent load/stores, then there could be
//     some rescheduling in between, whereas with `ldp` this is not the case (maybe tha load multiple
//     is kind of "atomic")
//
#[derive(PartialEq, Eq, Structural)] #[is_variant]
pub enum LoadResult {
    PageFault,
    // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
    Value(usize), // word-sized load
}

#[derive(PartialEq, Eq, Structural)] #[is_variant]
pub enum StoreResult {
    PageFault,
    // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
    Ok,
}

// operations on the kernel+hardware systems
// =========================================

// TODO sharing between processes, sharing domains
enum TransitionLabel {
    // SYSCALL
    // exception is device drivers that ask for a paddr
    //   - contiguous physical memory
    //
    // the user process cannot request aliased mappings
    // TODO Map { mappings: Set</* vaddr: */ nat>, flags: Flags, is_ok: bool },
 
    // consider MapDevice { mappings: Set</* vaddr: */ nat>, flags: Flags, is_ok: bool },

    // TODO do we need this? MapObject { mappings: Set</* vaddr: */ nat>, device_id: nat, flags: Flags, is_ok: bool },
    //   - a device can be currently modeled as a process Store/Load that hallucinates the correct vaddr
    // have a transaction that maps n pages as once

    // SYSCALL
    // one page
    // TODO Unmap { mappings: Set<nat>, is_ok: bool }, // TODO: 

    // SYSCALL
    // user processes do not lookup mappings, except for device drivers
    // Resolve { vaddr: nat, Result<(/* paddr: */ nat, Flags)> },

    // INSTRUCTION
    // write anywhere, on any length, maybe span two pages?
    // TODO: what happens if we straddle two pages and only one is mapped?
    // everything is persistent memory!
    // AVX gather scatter? if they are not atomic, just represent them with a seq of these
    IOOp { vaddr: nat, io_op: IoOp },
}


// TODO is the page table in memory?

pub enum IoOp {
    Store { new_value: usize, result: StoreResult }, // represents a third party doing a write too
    Load { is_exec: bool, result: LoadResult },
}

state_machine! { ProcessSystem {

    fields {
        pub usize_bytes: nat,
        pub bytes: Seq<usize>, // sequence of machine words
    }

    transition! {
        io_op(vaddr: nat, op: IoOp) {
            require(match op {
                IoOp::Store { new_value, result } => true,
                IoOp::Load { is_exec, result } => true,
            });
        }
    }

} }
