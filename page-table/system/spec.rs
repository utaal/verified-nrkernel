#[allow(unused_imports)] use crate::pervasive::*;
use crate::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use state_machines_macros::*;
use map::*;
use seq::*;

// == Trusted ==

#[derive(PartialEq, Eq, Structural)]
pub struct Flags {
    pub is_writable: bool,
    pub is_user_mode_allowed: bool,
    pub instruction_fetching_disabled: bool,
}


// TODO: this structure implies a transactional page-table

#[derive(PartialEq, Eq, Structural)]
pub struct PageTableEntry {
    pub region: crate::spec::MemRegion,
    pub flags: Flags,
}

state_machine! { MMU {
    fields {
        pub tlb: Map</* VAddr */ nat, PageTableEntry>,
        pub page_table: Map</* VAddr */ nat, PageTableEntry>,
    }

    readonly! {
        tlb_hit(vaddr: nat, paddr: nat, flags: Flags) {
            require(exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).region.size));
            let base = choose(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) >>=
                base <= vaddr && vaddr < base + pre.tlb.index(base).region.size);
            let entry = pre.tlb.index(base);
            require(flags == entry.flags);
            require(paddr == entry.region.base + (vaddr - base));
        }
    }

    readonly! {
        resolve_fail(vaddr: nat) {
            require(!exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).region.size));
            require(!exists(|base: nat| #[auto_trigger] pre.page_table.dom().contains(base) && base <= vaddr && vaddr < base + pre.page_table.index(base).region.size));
        }
    }

    transition! {
        fill_tlb(base: nat) {
            require(!pre.tlb.dom().contains(base));
            require(pre.page_table.dom().contains(base));
            update tlb = pre.tlb.insert(base, pre.page_table.index(base));
        }
    }

    transition! {
        invalidate_tlb_by_addr(base: nat) {
            require(pre.tlb.dom().contains(base));
            update tlb = pre.tlb.remove(base);
        }
    }

    transition! {
        update_page_table(new_page_table: Map<nat, PageTableEntry>) {
            update page_table = new_page_table;
        }
    }
} }

#[proof]
fn mmu_test_1() {
    let entry = PageTableEntry { region: crate::spec::MemRegion { base: 16, size: 8 }, flags: Flags { is_writable: true, is_user_mode_allowed: true, instruction_fetching_disabled: true } };
    let mt = MMU::State {
        tlb: map![],
        page_table: map![128 => entry],
    };
    let mt_p = MMU::State {
        tlb: map![128 => entry],
        ..mt
    };
    let t1 = MMU::Step::fill_tlb(128);
    // assert(MMU::State::fill_tlb(mt, mt_p, 128));
    // reveal(MMU::State::next_by);
    MMU::show::fill_tlb(mt, mt_p, 128);
    // assert(MMU::State::next_by(mt, mt_p, t1));
    assert(MMU::State::next(mt, mt_p));
}

// ===

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

pub enum IoOp {
    Store { new_value: Seq<u8> /* length 8 */, result: StoreResult }, // represents a third party doing a write too
    Load { is_exec: bool, result: LoadResult },
}

// TODO don't use choose
state_machine! { System {
    fields {
        pub mmu: MMU::State,
        pub physical_memory: Seq<u8>,
    }

    transition! {
        io_op(vaddr: nat, paddr: nat, op: IoOp, flags: Flags) {
            require(match op {
                IoOp::Store { new_value, result: store_result } => true &&
                    new_value.len() == 8,
                IoOp::Load { is_exec, result: load_result } => true,
            });
            require(exists(|post_mmu: MMU::State| MMU::State::tlb_hit(pre.mmu, post_mmu, vaddr, paddr, flags)));
            match op {
                IoOp::Store { new_value, result: store_result } => {
                    if flags.is_writable {
                        update physical_memory = choose(|s: Seq<u8>|
                            true
                            // TODO awful trigger
                            && #[trigger] s.len() == pre.physical_memory.len()
                            && forall(|i: nat| i < pre.physical_memory.len() >>=
                                (#[trigger] s.index(i)) == if i < paddr || i >= paddr + 8 {
                                    pre.physical_memory.index(i)
                                } else {
                                    new_value.index(i as int - paddr)
                                }));
                    } else {

                    }
                },
                IoOp::Load { is_exec, result: load_result } => {

                },
            }
        }
    }
} }
