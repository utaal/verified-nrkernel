#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use state_machines_macros::*;
use map::*;
use seq::*;
#[allow(unused_imports)] use set::*;
use crate::spec::MemRegion;

// state:
// - memory
// - pt memory
// - tlb
// transitions:
// - mem read/write
// - pt mem op
// - resolve --> this will be introduced in the composition state machine
// - tlb evict, tlb fill

verus! {

pub struct SystemVariables {
    mem:    Seq<nat>,
    pt_mem: Seq<nat>,
    tlb:    Map<nat,PageTableEntry>,
}

#[derive(PartialEq, Eq, Structural)]
pub struct Flags {
    pub is_writable: bool,
    pub is_user_mode_allowed: bool,
    pub instruction_fetching_disabled: bool,
}

#[derive(PartialEq, Eq, Structural)]
pub struct PageTableEntry {
    pub region: MemRegion,
    pub flags: Flags,
}

#[derive(PartialEq, Eq, Structural)] #[is_variant]
pub enum LoadResult {
    PageFault,
    // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
    Value(nat), // word-sized load
}

#[derive(PartialEq, Eq, Structural)] #[is_variant]
pub enum StoreResult {
    PageFault,
    // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
    Ok,
}

pub enum IoOp {
    Store { new_value: nat, result: StoreResult }, // represents a third party doing a write too
    Load { is_exec: bool, result: LoadResult },
}

enum SystemStep {
    IoOp { vaddr: nat, paddr: nat, op: IoOp },
    PTMemOp,
    TLBFill { base: nat, pte: PageTableEntry },
    TLBEvict { base: nat},
}

// Unaligned accesses are a bit funky with this index function and the word sequences but unaligned
// accesses can be thought of as two aligned accesses so it's probably fine at least until we
// consider concurrency.
spec fn word_index(idx: nat) -> nat {
    idx / 8
}

spec fn interp_pt_mem(pt_mem: Seq<nat>) -> Map<nat, PageTableEntry>;

spec fn init(s: SystemVariables) -> bool {
    s.tlb.dom() === Set::empty()
}

spec fn step_IoOp(s1: SystemVariables, s2: SystemVariables, vaddr: nat, paddr: nat, op: IoOp) -> bool {
    if exists|base: nat, pte: PageTableEntry| #![auto] s1.tlb.contains_pair(base,pte) && base <= vaddr && vaddr < base + pte.region.size {
        let (base, pte) = choose|p:(nat, PageTableEntry)| #![auto] s1.tlb.contains_pair(p.0,p.1) && p.0 <= vaddr && vaddr < p.0 + p.1.region.size;
        &&& paddr === (pte.region.base + (vaddr - base)) as nat
        &&& s2.tlb === s1.tlb
        &&& s2.pt_mem === s1.pt_mem
        &&& match op {
            IoOp::Store { new_value, result: StoreResult::Ok }        => {
                &&& pte.flags.is_user_mode_allowed
                &&& pte.flags.is_writable
                &&& s2.mem === s1.mem.update(word_index(paddr), new_value)
            }
            IoOp::Store { new_value, result: StoreResult::PageFault } => {
                &&& s2.mem === s1.mem
                &&& {
                    ||| !pte.flags.is_user_mode_allowed
                    ||| !pte.flags.is_writable
                }
            }
            IoOp::Load { is_exec, result: LoadResult::Value(n) }      => {
                &&& pte.flags.is_user_mode_allowed
                &&& (is_exec ==> !pte.flags.instruction_fetching_disabled)
                &&& s2.mem === s1.mem
                &&& n == s1.mem.index(word_index(paddr))
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
        &&& s2.tlb === s1.tlb
        &&& s2.pt_mem === s1.pt_mem
        &&& s2.mem === s1.mem
        &&& match op {
            IoOp::Store { new_value, result: StoreResult::Ok }        => false,
            IoOp::Store { new_value, result: StoreResult::PageFault } => true,
            IoOp::Load { is_exec, result: LoadResult::Value(n) }      => false,
            IoOp::Load { is_exec, result: LoadResult::PageFault }     => true,
        }
    }
}

spec fn step_PTMemOp(s1: SystemVariables, s2: SystemVariables) -> bool {
    &&& s2.mem === s1.mem
    &&& s2.tlb === s1.tlb
}

spec fn step_TLBFill(s1: SystemVariables, s2: SystemVariables, base: nat, pte: PageTableEntry) -> bool {
    &&& interp_pt_mem(s1.pt_mem).contains_pair(base, pte)
    &&& s2.tlb === s1.tlb.insert(base, pte)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

spec fn step_TLBEvict(s1: SystemVariables, s2: SystemVariables, base: nat) -> bool {
    &&& s1.tlb.dom().contains(base)
    &&& s2.tlb === s1.tlb.remove(base)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

spec fn next_step(s1: SystemVariables, s2: SystemVariables, step: SystemStep) -> bool {
    match step {
        SystemStep::IoOp { vaddr, paddr, op } => step_IoOp(s1, s2, vaddr, paddr, op),
        SystemStep::PTMemOp => step_PTMemOp(s1, s2),
        SystemStep::TLBFill { base, pte } => step_TLBFill(s1, s2, base, pte),
        SystemStep::TLBEvict { base } => step_TLBEvict(s1, s2, base),
    }
}

spec fn next(s1: SystemVariables, s2: SystemVariables) -> bool {
    exists|step: SystemStep| next_step(s1, s2, step)
}

spec fn inv(s: SystemVariables) -> bool {
    true
}

proof fn init_implies_inv(s: SystemVariables)
    requires
        init(s),
    ensures
        inv(s)
{ }

proof fn next_preserves_inv(s1: SystemVariables, s2: SystemVariables)
    requires
        next(s1, s2),
        inv(s1),
    ensures
        inv(s2),
{
    let step = choose|step: SystemStep| next_step(s1, s2, step);
    match step {
        SystemStep::IoOp { vaddr, paddr, op } => (),
        SystemStep::PTMemOp => (),
        SystemStep::TLBFill { base, pte } => (),
        SystemStep::TLBEvict { base } => (),
    }
}

}

// // == Trusted ==

// #[derive(PartialEq, Eq, Structural)]
// pub struct Flags {
//     pub is_writable: bool,
//     pub is_user_mode_allowed: bool,
//     pub instruction_fetching_disabled: bool,
// }


// // TODO: this structure implies a transactional page-table

// #[derive(PartialEq, Eq, Structural)]
// pub struct PageTableEntry {
//     pub region: crate::spec::MemRegion,
//     pub flags: Flags,
// }

// state_machine! { MMU {
//     fields {
//         pub tlb: Map</* VAddr */ nat, PageTableEntry>,
//         pub page_table: Map</* VAddr */ nat, PageTableEntry>,
//     }

//     readonly! {
//         tlb_hit(vaddr: nat, paddr: nat, flags: Flags) {
//             require(exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).region.size));
//             let base = choose(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) >>=
//                 base <= vaddr && vaddr < base + pre.tlb.index(base).region.size);
//             let entry = pre.tlb.index(base);
//             require(flags == entry.flags);
//             require(paddr == entry.region.base + (vaddr - base));
//         }
//     }

//     readonly! {
//         resolve_fail(vaddr: nat) {
//             require(!exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).region.size));
//             require(!exists(|base: nat| #[auto_trigger] pre.page_table.dom().contains(base) && base <= vaddr && vaddr < base + pre.page_table.index(base).region.size));
//         }
//     }

//     transition! {
//         fill_tlb(base: nat) {
//             require(!pre.tlb.dom().contains(base));
//             require(pre.page_table.dom().contains(base));
//             update tlb = pre.tlb.insert(base, pre.page_table.index(base));
//         }
//     }

//     transition! {
//         invalidate_tlb_by_addr(base: nat) {
//             require(pre.tlb.dom().contains(base));
//             update tlb = pre.tlb.remove(base);
//         }
//     }

//     transition! {
//         update_page_table(new_page_table: Map<nat, PageTableEntry>) {
//             update page_table = new_page_table;
//         }
//     }
// } }

// #[proof]
// fn mmu_test_1() {
//     let entry = PageTableEntry { region: crate::spec::MemRegion { base: 16, size: 8 }, flags: Flags { is_writable: true, is_user_mode_allowed: true, instruction_fetching_disabled: true } };
//     let mt = MMU::State {
//         tlb: map![],
//         page_table: map![128 => entry],
//     };
//     let mt_p = MMU::State {
//         tlb: map![128 => entry],
//         ..mt
//     };
//     let t1 = MMU::Step::fill_tlb(128);
//     // assert(MMU::State::fill_tlb(mt, mt_p, 128));
//     // reveal(MMU::State::next_by);
//     MMU::show::fill_tlb(mt, mt_p, 128);
//     // assert(MMU::State::next_by(mt, mt_p, t1));
//     assert(MMU::State::next(mt, mt_p));
// }

// // ===

// #[derive(PartialEq, Eq, Structural)] #[is_variant]
// pub enum LoadResult {
//     PageFault,
//     // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
//     Value(usize), // word-sized load
// }

// #[derive(PartialEq, Eq, Structural)] #[is_variant]
// pub enum StoreResult {
//     PageFault,
//     // BusError,  // maybe that's something to consider, e.g., the absence of bus errors ?
//     Ok,
// }

// pub enum IoOp {
//     Store { new_value: Seq<u8> /* length 8 */, result: StoreResult }, // represents a third party doing a write too
//     Load { is_exec: bool, result: LoadResult },
// }

// // TODO don't use choose
// state_machine! { System {
//     fields {
//         pub mmu: MMU::State,
//         pub physical_memory: Seq<u8>,
//     }

//     transition! {
//         io_op(vaddr: nat, paddr: nat, op: IoOp, flags: Flags) {
//             require(match op {
//                 IoOp::Store { new_value, result: store_result } => true &&
//                     new_value.len() == 8,
//                 IoOp::Load { is_exec, result: load_result } => true,
//             });
//             require(exists(|post_mmu: MMU::State| MMU::State::tlb_hit(pre.mmu, post_mmu, vaddr, paddr, flags)));
//             match op {
//                 IoOp::Store { new_value, result: store_result } => {
//                     if flags.is_writable {
//                         update physical_memory = choose(|s: Seq<u8>|
//                             true
//                             // TODO awful trigger
//                             && #[trigger] s.len() == pre.physical_memory.len()
//                             && forall(|i: nat| i < pre.physical_memory.len() >>=
//                                 (#[trigger] s.index(i)) == if i < paddr || i >= paddr + 8 {
//                                     pre.physical_memory.index(i)
//                                 } else {
//                                     new_value.index(i as int - paddr)
//                                 }));
//                     } else {

//                     }
//                 },
//                 IoOp::Load { is_exec, result: load_result } => {

//                 },
//             }
//         }
//     }
// } }
