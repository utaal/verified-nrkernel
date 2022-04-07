

struct OS {
}

// MemRegion: address, size

// invariant: not map the page table accessible from userspace
impl OS {
    // this is a model of syscall
    // one page
    pub transition(self, post: Self, transition: TransitionLabel)
    // have a transaction that maps n pages as once
}

enum LoadResult {
    PageFault,
    Value(value)
}

enum TransitionLabel {
    // SYSCALL
    Map(vaddr, paddr, page_size, flags: FLAGS, is_ok)
    // have a transaction that maps n pages as once

    // SYSCALL
    // one page
    Unmap(vaddr, is_ok)

    // SYSCALL
    // lookup a mapping
    Resolve(vaddr, Result<(paddr, size, FLAGS)>)

    // INSTRUCTION
    // write anywhere, on any length, maybe span two pages?
    // TODO: what happens if we straddle two pages and only one is mapped?
    // everything is persistent memory!
    // AVX gather scatter? if they are not atomic, just represent them with a seq of these
    IOOp(vaddr, size,
        Store(new_value, page_fault), // represents a third party doing a write too
        Load(is_exec, result: LoadResult),
        )
}

// ------
//
//
struct MemoryTranslator {

}

struct Memory {

}

impl MemoryTranslator { // and TLB?
    fn translate(self, post, vaddr, paddr)   // this is the walker
}

impl Memory {
    fn ...
}

struct Env {
    page_table: _,

    tlb: _,

}

// Bottom bread
// composition of program with its environment
struct ExecutableSystem<P: Program /* represents multiple programs */, T: OSImpl> {
    program: P, // transition labels
    os: T,
    env: Env,
}

// Trusted assembler that passes the map syscall to rust
// API boundary


