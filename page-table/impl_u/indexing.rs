#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use modes::*;
use seq::*;
use option::{*, Option::*};
use map::*;
use set::*;
use set_lib::*;
use vec::*;
use result::{*, Result::*};
use crate::impl_u::lib;
use crate::definitions_t::{ aligned, between };

verus! {

///! This module implements an indexing calculus with corresponding lemmas. It only provides spec
///! functions, without any exec versions. The (specialized to specific entry_size) exec versions
///! can be implemented in their own modules and simply assert their equivalence to these spec
///! functions to make use of the lemmas. This is mainly because the absence of overflows may use
///! different bounds depending on the exact context. It also has the benefit that trusted exec
///! functions (e.g. in mem) are fully defined in their own modules


// pub fn index_from_offset(offset: usize, entry_size: usize) -> (res: usize)
//     requires
//         entry_size > 0,
//     ensures
//         res as nat === index_from_offset_spec(offset, entry_size)
// {
//     let res = offset / entry_size;
//     assume(false);
//     res
// }

pub open spec fn index_from_offset(offset: nat, entry_size: nat) -> (res: nat)
    recommends
        entry_size > 0,
{
    offset / entry_size
}

// /// Compute `(addr - base) / entry_size`
// pub fn index_from_base_and_addr(base: usize, addr: usize, entry_size: usize) -> (res: usize)
//     requires
//         addr >= base,
//         entry_size > 0,
//     ensures
//         res as nat === index_from_base_and_addr_spec(base, addr, entry_size)
// {
//     let offset = addr - base;
//     let res = index_from_offset(offset, entry_size);
//     res
// }

pub open spec fn index_from_base_and_addr(base: nat, addr: nat, entry_size: nat) -> nat
    recommends
        addr >= base,
        entry_size > 0,
{
    index_from_offset(sub(addr, base), entry_size)
}

// /// Compute `base + idx * entry_size`
// #[verifier(nonlinear)]
// pub fn entry_base_from_index(base: usize, idx: usize, entry_size: usize) -> (res: usize)
//     // FIXME: Are these bounds okay for the memory indexing?
//     requires
//         base       < 0x8000_0000_0000_0000, // 2^63
//         idx        < 0x8000_0000_0000_0000, // 2^63
//         idx        <= 0x100_0000, // 2^24
//         entry_size <= 0x80_0000_0000, // 2^39
//     ensures
//         res == entry_base_from_index_spec(base, idx, entry_size)
// {
//     base + idx * entry_size
// }

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

pub open spec fn nat_mul(a: nat, b: nat) -> nat {
    a * b
}

// This lemma has "support" postconditions for lemma_entry_base_from_index. I.e. postconditions
// that may help proving the lhs of some of that lemma's postconditions which are implications.
// However, one of these postconditions triggers on every multiplication, hence this is separated
// in its own lemma.
pub proof fn lemma_entry_base_from_index_support(base: nat, idx: nat, entry_size: nat)
    ensures
        // forall|nested_es: nat, nested_num: nat|
        //     entry_size == nat_mul(nested_es, nested_num)
        //     ==> next_entry_base_from_index(base, idx, entry_size)
        //         == entry_base_from_index(entry_base_from_index(base, idx, entry_size), nested_num, nested_es),
        // Support postconditions:
        // Ugly, ugly workaround for mixed triggers.
        forall_arith(|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b)),
        forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a),
        forall|a: nat| #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0 ==> aligned(base, entry_size),
{
    assert(forall_arith(|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b))) by(nonlinear_arith);
    assert(forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a)) by(nonlinear_arith);
    assert forall|a: nat|
        #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0
        implies
        aligned(base, entry_size) by
    {
        lib::mod_mult_zero_implies_mod_zero(base, entry_size, a);
    };
}

pub proof fn lemma_entry_base_from_index(base: nat, idx: nat, entry_size: nat)
    ensures
        forall|idx2: nat|
            #![trigger entry_base_from_index(base, idx, entry_size), entry_base_from_index(base, idx2, entry_size)]
            idx < idx2 ==> entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size),
                   // // && next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(layer, base, j),
        // TODO: The line above can't be a separate postcondition because it doesn't have any valid triggers.
        // The trigger for it is pretty bad.
        forall|idx2: nat| idx < idx2
            ==> next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx + 1, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx, entry_size) + entry_size,
        next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(base, idx, entry_size),
        forall|n: nat|
            aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n),
        forall|n: nat|
            aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n),
        aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size),
        base <= entry_base_from_index(base, idx, entry_size),
        // forall|idx: nat, base: nat, layer: nat|
        //     layer < self.layers.len() && idx < self.num_entries(layer) ==> entry_base_from_index(base, idx, entry_size) < self.upper_vaddr(layer, base),
        // forall|idx: nat, base: nat, layer: nat|
            // layer < self.layers.len() && idx <= self.num_entries(layer) ==> entry_base_from_index(base, idx, entry_size) <= self.upper_vaddr(layer, base),
        // forall|idx: nat, base: nat, layer: nat|
            // layer + 1 < self.layers.len() ==> #[trigger] next_entry_base_from_index(base, idx, entry_size) == self.upper_vaddr(layer + 1, entry_base_from_index(base, idx, entry_size)),
        // // Support postconditions:
        // forall_arith(|base: nat, n: nat| // Used to infer lhs of next postcondition's implication
        //     aligned(base, #[trigger] (entry_size * n)) ==> aligned(base, entry_size)),
        // No valid triggers
        // Note for thesis report:
        // This is really annoying. No mixed triggers means I can't use this postcondition. In the
        // less general case (lemma_entry_base) this worked because n happens to be a specific
        // function call there on which we can trigger. In other words: the lack of mixed triggers
        // makes it impossible to generalize this postcondition.
{
        assert forall|idx2: nat|
            idx < idx2
            implies entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size) by
        {
            assert(entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size))
                by(nonlinear_arith)
                requires
                    idx < idx2
            {
                // FIXME:
                assume(false);
            };
        };
        assert forall|idx2: nat|
            idx < idx2
            implies next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size) by
        {
            assert(next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size))
                by(nonlinear_arith)
                requires
                    idx < idx2
            {
            };
        };
        assert(next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx + 1, entry_size));
        assert(next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx, entry_size) + entry_size) by(nonlinear_arith);
        assert(next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(base, idx, entry_size));
        assert forall|n: nat|
            aligned(base, n) && aligned(entry_size, n)
            implies #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n) by
        {
            assert(aligned(entry_base_from_index(base, idx, entry_size), n))
                by(nonlinear_arith)
                requires
                    aligned(base, n),
                    aligned(entry_size, n)
            {
                // FIXME:
                assume(false);
            };
        };
        assert forall|n: nat|
            aligned(base, n) && aligned(entry_size, n)
            implies #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n) by
        {
            assert(aligned(next_entry_base_from_index(base, idx, entry_size), n))
                by(nonlinear_arith)
                requires
                    aligned(base, n),
                    aligned(entry_size, n)
            {
                // FIXME:
                assume(false);
            };
        };
        assert(aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size));
        assert(base <= entry_base_from_index(base, idx, entry_size));
}

pub proof fn lemma_index_from_base_and_addr(base: nat, addr: nat, entry_size: nat, num_entries: nat)
    requires
        addr >= base,
        addr < entry_base_from_index(base, num_entries, entry_size),
        entry_size > 0,
    ensures
        ({
            let idx = index_from_base_and_addr(base, addr, entry_size);
            &&& idx < num_entries
            &&& between(addr, entry_base_from_index(base, idx, entry_size), next_entry_base_from_index(base, idx, entry_size))
            &&& aligned(addr, entry_size) ==> addr == entry_base_from_index(base, idx, entry_size)
        }),
{
    assume(false);
    // // FIXME: prove all this stuff
    // let idx = self.index_for_vaddr(layer, base, vaddr);
    // assert(idx < self.num_entries(layer)) by(nonlinear_arith)
    //     requires
    //         self.inv(),
    //         layer < self.layers.len(),
    //         between(vaddr, base, self.upper_vaddr(layer, base)),
    //         idx == self.index_for_vaddr(layer, base, vaddr),
    // { };
    // assert(between(vaddr, self.entry_base(layer, base, idx), self.next_entry_base(layer, base, idx))) by(nonlinear_arith)
    //     requires
    //         self.inv(),
    //         layer < self.layers.len(),
    //         between(vaddr, base, self.upper_vaddr(layer, base)),
    //         idx == self.index_for_vaddr(layer, base, vaddr),
    //         idx < self.num_entries(layer),
    // { };
    // assert(aligned(vaddr, self.entry_size(layer)) ==> vaddr == self.entry_base(layer, base, idx)) by (nonlinear_arith)
    //     requires
    //         self.inv(),
    //         layer < self.layers.len(),
    //         base <= vaddr,
    //         vaddr < self.upper_vaddr(layer, base),
    //         idx == self.index_for_vaddr(layer, base, vaddr),
    //         idx < self.num_entries(layer),
    //         between(vaddr, self.entry_base(layer, base, idx), self.next_entry_base(layer, base, idx)),
    // {
    //     assume(false);
    // };
    // assert(idx < MAX_NUM_ENTRIES);
}
}
