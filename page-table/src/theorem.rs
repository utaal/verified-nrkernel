use vstd::prelude::*;
use crate::spec_t::hlspec;
use crate::spec_t::os;
use crate::spec_t::mmu::defs::{ MemOp, PTE };

verus!{

// Lemma 1: OS state machine with the atomic MMU refines the high-level spec

pub enum TokState {
    Init,
    ProphecyMade,
    Validated,
    Spent,
}

pub enum RLbl {
    Tau,
    MemOp      { thread_id: nat, vaddr: nat, op: MemOp },
    MapStart   { thread_id: nat, vaddr: nat, pte: PTE },
    MapEnd     { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    UnmapStart { thread_id: nat, vaddr: nat },
    UnmapEnd   { thread_id: nat, vaddr: nat, result: Result<(), ()> },
}

proof fn lemma1_init(c: os::Constants, pre: os::State)
    requires os::init(c, pre)
    ensures hlspec::init(c.interp(), pre.interp(c))
{
    admit();
}

proof fn lemma1_next(
    c: os::Constants,
    pre: os::State,
    post: os::State,
    lbl: RLbl,
)
    requires os::next(c, pre, post, lbl)
    ensures hlspec::next(c.interp(), pre.interp(c), post.interp(c), lbl)
{
    admit();
}

// Lemma 2: Concrete MMU refines the atomic MMU
// TODO: interp function that skips directly to rl1

//proof fn lemma2_init(c: mmu::Constants, pre: mmu::rl4::State)
//    requires pre.init()
//    ensures pre.interp().interp().interp().init()
//{
//    admit();
//}

//proof fn lemma2_next(
//    c: mmu::Constants,
//    pre: mmu::rl4::State,
//    post: mmu::rl4::State,
//    lbl: mmu::Lbl,
//)
//    requires mmu::rl4::next(pre, post, c, lbl)
//    ensures mmu::rl1::next(pre.interp().interp().interp(), post.interp().interp().interp(), c, lbl)
//{
//    admit();
//}

// Lemma 3: The implementation refines the implementation behavior specified in the OS state machine
//
// TODO:

}
