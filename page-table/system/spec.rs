#[allow(unused_imports)] use crate::pervasive::*;
use crate::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use state_machines_macros::*;
use map::*;

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
    pub p_addr: nat,
    pub size: nat,
    pub flags: Flags,
}

state_machine! { MemoryTranslator {
    fields {
        pub tlb: Map</* VAddr */ nat, PageTableEntry>,
        pub page_table: Map</* VAddr */ nat, PageTableEntry>,
    }

    readonly! {
        tlb_hit(vaddr: nat, p_addr: nat, flags: Flags) {
            require(exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).size));
            let base = choose(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) >>=
                base <= vaddr && vaddr < base + pre.tlb.index(base).size);
            let entry = pre.tlb.index(base);
            require(flags == entry.flags);
            require(p_addr == entry.p_addr + (vaddr - base));
        }
    }

    readonly! {
        resolve_fail(vaddr: nat) {
            require(!exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).size));
            require(!exists(|base: nat| #[auto_trigger] pre.page_table.dom().contains(base) && base <= vaddr && vaddr < base + pre.page_table.index(base).size));
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
            update tlb = pre.tlb.remove(base);
        }
    }

    transition! {
        invalidate_tlb_full() {
            // TODO(andrea) update tlb = map![];
        }
    }

    // operation to flush by context identifier

    transition! {
        // root of the page table stays the same; this is "just" updating some entries, not a
        // context switch
        //
        // RA: do we need something like `set_entry` ?
        update_page_table(new_page_table: Map<nat, PageTableEntry>) {
            update page_table = new_page_table;
        }
    }

    // TODO: flush range?

    // RA: We assume that the hardware is always enabled.
    //     This is fine, as this is what it is during normal mode of operation after initalization.
    // | Yes!
} }

#[proof]
fn memory_translator_test_1() {
    let entry = PageTableEntry { p_addr: 16, size: 8, flags: Flags { is_writable: true, is_user_mode_allowed: true, instruction_fetching_disabled: true } };
    let mt = MemoryTranslator::State {
        tlb: map![],
        page_table: map![128 => entry],
    };
    let mt_p = MemoryTranslator::State {
        tlb: map![128 => entry],
        ..mt
    };
    // assert(MemoryTranslator::Step::fill_tlb(mt, mt_p, 128));
    let s1 = MemoryTranslator::Step::fill_tlb(128);
    // assert(MemoryTranslator::Step::resolve_fail(mt, 128, entry));
}




// impl MemoryTranslator { // and TLB?
//     fn translate(self, post, vaddr, paddr)   // this is the walker
// }
//
// impl Memory {
//     fn ...
// }
//
// struct Env {
//     page_table: _,
//
//     tlb: _,
//
// }
//
// // Bottom bread
// // composition of program with its environment
// struct ExecutableSystem<P: Program /* represents multiple programs */, T: OSImpl> {
//     program: P, // transition labels
//     os: T,
//     env: Env,
// }
//
// // Trusted assembler that passes the map syscall to rust
// // API boundary
//
//
