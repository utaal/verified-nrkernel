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
struct Flags {
    is_present: bool, // walker aborts if !is_present
    is_writable: bool,
    is_user_mode_allowed: bool,
    instruction_fetching_disabled: bool,
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

#[derive(PartialEq, Eq, Structural)] #[is_variant]
enum LoadResult {
    PageFault,
    Value(usize), // word-sized load
}

#[derive(PartialEq, Eq, Structural)] #[is_variant]
enum StoreResult {
    PageFault,
    Ok,
}
 
// enum TransitionLabel {
//     // SYSCALL
//     Map(vaddr, paddr, page_size, flags: Flags, is_ok)
//     // have a transaction that maps n pages as once
// 
//     // SYSCALL
//     // one page
//     Unmap(vaddr, is_ok)
// 
//     // SYSCALL
//     // lookup a mapping
//     Resolve(vaddr, Result<(paddr, size, Flags)>)
// 
//     // INSTRUCTION
//     // write anywhere, on any length, maybe span two pages?
//     // TODO: what happens if we straddle two pages and only one is mapped?
//     // everything is persistent memory!
//     // AVX gather scatter? if they are not atomic, just represent them with a seq of these
//     IOOp(vaddr, size,
//         Store(new_value, result: StoreResult), // represents a third party doing a write too
//         Load(is_exec, result: LoadResult),
//         )
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
#[derive(PartialEq, Eq, Structural)]
pub struct PageTableEntry {
    p_addr: nat,
    size: nat,
    flags: Flags,
}

state_machine! { MemoryTranslator {
    fields {
        pub tlb: Map</* VAddr */ nat, PageTableEntry>, // all the VAddr of a page move in sync
        pub page_table: Map</* VAddr */ nat, PageTableEntry>,
    }

    readonly! {
        resolve(vaddr: nat, entry: PageTableEntry) {
            require(pre.tlb.dom().contains(vaddr));
            require(entry == pre.tlb.index(vaddr));
        }
    }

    transition! {
        fill_tlb(vaddr: nat) {
            require(pre.page_table.dom().contains(vaddr));
            update tlb = pre.tlb.insert(vaddr, pre.page_table.index(vaddr));
        }
    }

    // TODO: do we want a next transition?
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
    // TODO ??? assert(MemoryTranslator::Step::fill_tlb(mt, mt_p, 128));
    // TODO ??? assert(MemoryTranslator::Step::resolve(mt, 128, entry));
}

// impl MemoryTranslator {
// 
//     fn invalidate(self, self', ) {
// 
//         // 
//     }
// 
//     fn fill_tlb(self, self', ) {
// 
//         // TODO: is this always tied to a memory operation
//         // Jon was suggesting this is always nondeterministic
//         // TODO: this could be the invalidate op too!
//     }
// 
//     fn resolve(self, self', vaddr: nat, PAddr, size: nat, Flags) {
//         requires(self.tlb.contains(vaddr))
// 
//     }
// 
//     // TODO: does this work with the overall system model
//     fn switch_page_table(self, self', Map<>) {
// 
//     }
// 
// }
// 
// struct Memory {
// 
// }
// 
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
