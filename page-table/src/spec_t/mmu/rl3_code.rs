#![verus::trusted]
// Trusted: This file defines the trusted interface to the hardware

use vstd::prelude::*;
use crate::spec_t::mmu::rl3;
//use crate::spec_t::mem::word_index_spec;
use crate::spec_t::mmu::{ self, Core };
//use crate::spec_t::mmu::pt_mem::*;
//use crate::spec_t::mmu::defs::{ aligned, bit, Core, bitmask_inc, HWMemOp, HWLoadResult, PTE };
//use crate::spec_t::mmu::translation::{ l0_bits, l1_bits, l2_bits, l3_bits, MASK_DIRTY_ACCESS };

verus! {
    #[verifier(external_body)]
    pub tracked struct Token {}

    #[verifier(external_body)]
    pub tracked struct Stub {}

    impl Token {
        pub spec fn constants(self) -> mmu::Constants;
        pub spec fn pre(self) -> rl3::State;
        pub spec fn core(self) -> Core;
    }

    impl Stub {
        pub spec fn post(self) -> rl3::State;
        pub spec fn lbl(self) -> mmu::Lbl;
    }

    #[verifier(external_body)]
    pub exec fn read(Tracked(tok): Tracked<Token>, addr: usize)
       -> (res:
           (Tracked<Stub>, // stub
            Ghost<usize>,  // r
            usize))        // value
        ensures
            rl3::step_Read(tok.pre(), res.0@.post(), tok.constants(), res.1@, res.0@.lbl()),
            res.0@.lbl() == mmu::Lbl::Read(tok.core(), addr, res.2),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub exec fn write(Tracked(tok): Tracked<Token>, addr: usize, value: usize) -> (stub: Tracked<Stub>)
        ensures
            rl3::step_Write(tok.pre(), stub@.post(), tok.constants(), stub@.lbl()),
            stub@.lbl() == mmu::Lbl::Write(tok.core(), addr, value),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub exec fn barrier(Tracked(tok): Tracked<Token>) -> (stub: Tracked<Stub>)
        ensures
            rl3::step_Barrier(tok.pre(), stub@.post(), tok.constants(), stub@.lbl()),
            stub@.lbl() == mmu::Lbl::Barrier(tok.core()),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub exec fn invlpg(Tracked(tok): Tracked<Token>, vaddr: usize) -> (stub: Tracked<Stub>)
        ensures
            rl3::step_Invlpg(tok.pre(), stub@.post(), tok.constants(), stub@.lbl()),
            stub@.lbl() == mmu::Lbl::Invlpg(tok.core(), vaddr),
    {
        unimplemented!()
    }

    // TODO: need transitions to allocate/deallocate pages i guess
    // TODO: add a transition to read pml4?
    //#[verifier(external_body)]
    //pub exec fn get_pml4(Tracked(tok): Tracked<Token>, vaddr: usize) -> (stub: Tracked<Stub>)
    //    ensures ..
    //{
    //    unimplemented!()
    //}


} // verus!
