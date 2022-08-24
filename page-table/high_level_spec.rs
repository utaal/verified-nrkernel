#![allow(unused_imports)]
use crate::pervasive::*;
use seq::*;
use crate::*;
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use map::*;
use crate::aux_defs::{overlap, MemRegion, PageTableEntry, Flags};

// state:
// - memory
// transitions:
// - mem read/write
// - map/unmap
// - resolve

// TODO:
// - should Map be able to set is_user_mode_allowed?

verus! {

pub struct AbstractVariables {
    pub mem: Map<nat,nat>, // word-indexed
    /// `mappings` constrains the domain of mem. We could instead move the flags into `map` as well
    /// and write the specification exclusively in terms of `map` but that also makes some of the
    /// preconditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat,PageTableEntry>
}

#[derive(PartialEq, Eq, Structural)] #[is_variant]
pub enum LoadResult {
    PageFault,
    Value(nat), // word-sized load
}

#[derive(PartialEq, Eq, Structural)] #[is_variant]
pub enum StoreResult {
    PageFault,
    Ok,
}

pub enum IoOp {
    Store { new_value: nat, result: StoreResult },
    Load { is_exec: bool, result: LoadResult },
}

pub enum AbstractStep {
    IoOp  { vaddr: nat, op: IoOp },
    Map   { base: nat, pte: PageTableEntry },
    Unmap { base: nat },
    // Resolve { vaddr: nat }, // How do we specify this?
}

// Unaligned accesses are a bit funky with this index function and the word sequences but unaligned
// accesses can be thought of as two aligned accesses so it's probably fine at least until we
// consider concurrency.
pub open spec fn word_index(idx: nat) -> nat {
    idx / 8
}

pub open spec fn init(s: AbstractVariables) -> bool {
    s.mem === Map::empty() // TODO: maybe change this
}

// TODO: also use this in system spec
/// Returns `true` if m contains a mapping for `base` and `vaddr` is within the range of that mapping
pub open spec fn mapping_contains(m: Map<nat, PageTableEntry>, base: nat, vaddr: nat) -> bool {
    m.dom().contains(base) && base <= vaddr && vaddr < base + m.index(base).frame.size
}

pub open spec fn step_IoOp(s1: AbstractVariables, s2: AbstractVariables, vaddr: nat, op: IoOp) -> bool {
    &&& s2.mappings === s1.mappings
    &&& if exists|base: nat| mapping_contains(s1.mappings, base, vaddr) {
        let base    = choose|base: nat| mapping_contains(s1.mappings, base, vaddr);
        let pte     = s1.mappings.index(base);
        let mem_idx = word_index(vaddr);
        let mem_val = s1.mem.index(mem_idx);
        match op {
            IoOp::Store { new_value, result: StoreResult::Ok }        => {
                &&& pte.flags.is_user_mode_allowed
                &&& pte.flags.is_writable
                &&& s2.mem === s1.mem.insert(mem_idx, new_value)
            }
            IoOp::Store { new_value, result: StoreResult::PageFault } => {
                &&& {
                    ||| !pte.flags.is_user_mode_allowed
                    ||| !pte.flags.is_writable
                }
                &&& s2.mem === s1.mem
            }
            IoOp::Load { is_exec, result: LoadResult::Value(n) }      => {
                &&& pte.flags.is_user_mode_allowed
                &&& (is_exec ==> !pte.flags.instruction_fetching_disabled)
                &&& s2.mem === s1.mem
                &&& n == mem_val
            },
            IoOp::Load { is_exec, result: LoadResult::PageFault }     => {
                &&& s2.mem === s1.mem
                &&& {
                    ||| !pte.flags.is_user_mode_allowed
                    ||| (is_exec && pte.flags.instruction_fetching_disabled)
                }
            },
        }
    } else {
        match op {
            IoOp::Store { new_value, result: StoreResult::PageFault } => s2.mem === s1.mem,
            IoOp::Load  { is_exec, result: LoadResult::PageFault }    => s2.mem === s1.mem,
            _                                                         => false,
        }
    }
}

pub open spec fn step_Map(s1: AbstractVariables, s2: AbstractVariables, base: nat, pte: PageTableEntry) -> bool {
    &&& true // TODO: alignment, anything else?
    &&& forall|base2: nat, pte2|
        #[trigger] s1.mappings.contains_pair(base2, pte2)
        ==> !overlap(MemRegion { base, size: pte.frame.size }, MemRegion { base: base2, size: pte2.frame.size })
    &&& s2.mem === s1.mem
    &&& s2.mappings === s1.mappings.insert(base, pte)
}

pub open spec fn step_Unmap(s1: AbstractVariables, s2: AbstractVariables, base: nat) -> bool {
    &&& true // TODO: anything else?
    &&& s1.mappings.dom().contains(base)
    &&& s1.mappings.index(base).flags.is_user_mode_allowed
    &&& s2.mem === s1.mem
    &&& s2.mappings === s1.mappings.remove(base)
}

pub open spec fn next_step(s1: AbstractVariables, s2: AbstractVariables, step: AbstractStep) -> bool {
    match step {
        AbstractStep::IoOp  { vaddr, op } => step_IoOp(s1, s2, vaddr, op),
        AbstractStep::Map   { base, pte } => step_Map(s1, s2, base, pte),
        AbstractStep::Unmap { base }      => step_Unmap(s1, s2, base),
    }
}

pub open spec fn next(s1: AbstractVariables, s2: AbstractVariables) -> bool {
    exists|step: AbstractStep| next_step(s1, s2, step)
}

}

// // RA: the ARMv8 architecture you can also load/store a pair of registers in one instruction,
// //     (and I think even more than that)
// //
// //     now these are technically two loads/stores as I assume.  From the manual (C6.2.130 LDP):
// //      data1 = Mem[address, dbytes, AccType_NORMAL];
// //      data2 = Mem[address+dbytes, dbytes, AccType_NORMAL];
// //      X[t] = data1;
// //      X[t2] = data2;
// //
// //     the ARMv7 has a load multiple.
// //
// //     the other thing to consider here would be the SIMD registers, where we can do a
// //     load/store of up to 512bits.
// //
// //     I think conceptually we could say that this will be just two load/stores. Though, the
// //     difference here may be subtle, if you do two independent load/stores, then there could be
// //     some rescheduling in between, whereas with `ldp` this is not the case (maybe tha load multiple
// //     is kind of "atomic")
// //
// #[derive(PartialEq, Eq, Structural)] #[is_variant]
// pub enum LoadResult {
//     PageFault,
//     // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
//     Value(usize), // word-sized load
// }
// 
// #[derive(PartialEq, Eq, Structural)] #[is_variant]
// pub enum StoreResult {
//     PageFault,
//     // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
//     Ok,
// }
// 
// // operations on the kernel+hardware systems
// // =========================================
// 
// // TODO sharing between processes, sharing domains
// enum TransitionLabel {
//     // SYSCALL
//     // exception is device drivers that ask for a paddr
//     //   - contiguous physical memory
//     //
//     // the user process cannot request aliased mappings
//     // TODO Map { mappings: Set</* vaddr: */ nat>, flags: Flags, is_ok: bool },
//  
//     // consider MapDevice { mappings: Set</* vaddr: */ nat>, flags: Flags, is_ok: bool },
// 
//     // TODO do we need this? MapObject { mappings: Set</* vaddr: */ nat>, device_id: nat, flags: Flags, is_ok: bool },
//     //   - a device can be currently modeled as a process Store/Load that hallucinates the correct vaddr
//     // have a transaction that maps n pages as once
// 
//     // SYSCALL
//     // one page
//     // TODO Unmap { mappings: Set<nat>, is_ok: bool }, // TODO: 
// 
//     // SYSCALL
//     // user processes do not lookup mappings, except for device drivers
//     // Resolve { vaddr: nat, Result<(/* paddr: */ nat, Flags)> },
// 
//     // INSTRUCTION
//     // write anywhere, on any length, maybe span two pages?
//     // TODO: what happens if we straddle two pages and only one is mapped?
//     // everything is persistent memory!
//     // AVX gather scatter? if they are not atomic, just represent them with a seq of these
//     IOOp { vaddr: nat, io_op: IoOp },
// }
// 
// 
// // TODO is the page table in memory?
// 
// pub enum IoOp {
//     Store { new_value: usize, result: StoreResult }, // represents a third party doing a write too
//     Load { is_exec: bool, result: LoadResult },
// }
// 
// state_machine! { ProcessSystem {
// 
//     fields {
//         pub usize_bytes: nat,
//         pub bytes: Seq<usize>, // sequence of machine words
//     }
// 
//     transition! {
//         io_op(vaddr: nat, op: IoOp) {
//             require(match op {
//                 IoOp::Store { new_value, result } => true,
//                 IoOp::Load { is_exec, result } => true,
//             });
//         }
//     }
// 
// } }
