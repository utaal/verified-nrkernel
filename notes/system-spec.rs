#[allow(unused_imports)] use crate::pervasive::*;
use crate::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use state_machines_macros::*;
use map::*;


// struct OS {
// }

// MemRegion: address, size
// from https://github.com/gz/rust-x86/blob/master/src/bits64/paging.rs#L1237
#[derive(PartialEq, Eq, Structural)]
pub struct Flags {
    pub is_present: bool, // walker aborts if !is_present
    pub is_writable: bool,
    pub is_user_mode_allowed: bool,
    pub instruction_fetching_disabled: bool,
}


//
//     is_pat flag
//
// // invariant: not map the page table accessible from userspace
// impl OS {
//     // this is a model of syscall
//     // one page
//     pub transition(self, post: Self, transition: TransitionLabel)
//     // have a transaction that maps n pages as once
// }
//


// // PageFault?
// //  |
// //  | IOOp(vaddr, size, Store(12, page_fault=true))
// //  |
// //  | Map(vaddr, ...)
//
// // ------
// //
// //
//


// == Trusted ==

// TODO: this structure implies a transactional page-table

#[derive(PartialEq, Eq, Structural)]
pub struct PageTableEntry {
    pub p_addr: nat,
    pub size: nat,
    pub flags: Flags,
    // track context identifiers
}

// Matthias: consider using a more close-to-the-hardware representation for the page table

// This model assumes "linearizability" of the memory subsystem, in particular it
// assumes monotonic observations (no non-monotonic reads)
//
// If this assumption doesn't hold, we may need start/end operation transitions (e.g. request
// initiated, resolution complete)
//
// RA| state: IDLE | START_RESOLVING(vaddr) | REFILLING(VADDR) | RESOLVED_SUCCESS(vaddr, paddr) | RESOLVED_FAILURE ?
//   | maybe there is a map<Vaddr, ResolveState> where the number of entries are the parallel resolves?
state_machine! { MemoryTranslator {
    fields {
        // the tlb
        pub tlb: Map</* VAddr */ nat, PageTableEntry>, // all the VAddr of a page move in sync
            // NOTE: drity/accessed bits are probably not in the TLB (as there's no explicit write-back)
            // | maybe this is only relevant for dirty/accessed bits

        // RA: not sure whether we should call this "page_table_walker" or alike?
        //
        // Do we need to represent intermediate state when the page table is being changed by
        // successive memory operations?
        pub page_table: Map</* VAddr */ nat, PageTableEntry>,
    }

    // RA: somehow right now we have a resolve that requires the TLB to contain an entry,
    //     and a fill_tlb that requires the TLB not to contain an entry. I think that should be fine?
    //     or do we need something like a fill then resolve?
    // | When are the dirty/accessed bits set on the TLB vs the page-table.
    // | Does the TLB have a "cache" of the dirty/accessed bits? Do they need to be written back?

    // RA: resolve may actually also change the TLB state (or even the page table)
    //     w.r.t. the accessed/dirty bits or alike.
    // | only for accessed/dirty bits, which we don't need yet

    readonly! {
        tlb_hit(vaddr: nat, p_addr: nat, flags: Flags) {
            require(exists(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) && base <= vaddr && vaddr < base + pre.tlb.index(base).size));
            let base = choose(|base: nat| #[auto_trigger] pre.tlb.dom().contains(base) >>=
                base <= vaddr && vaddr < base + pre.tlb.index(base).size);
            let entry = pre.tlb.index(base);
            // RA: that could be a bit too strinct, say, the entry allows read and write,
            //     but you only want to resolve read-only.
            require(flags == entry.flags);
            require(p_addr == entry.p_addr + (vaddr - base));
        }
    }

    // RA: wouldn't here resolve not be something like
    //       resolve(vaddr, ResolveResult)?
    //     or how do we express that resolve may fail?
    // | tlb_miss:
    // |    - resolve_fail
    // | or - fill_tlb -> tlb_hit

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
    let entry = PageTableEntry { p_addr: 16, size: 8, flags: Flags { is_present: true, is_writable: true, is_user_mode_allowed: true, instruction_fetching_disabled: true } };
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
