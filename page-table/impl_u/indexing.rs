use vstd::prelude::*;
use crate::extra;
use crate::definitions_t::{ aligned, between, index_from_offset, index_from_base_and_addr, entry_base_from_index, next_entry_base_from_index };

verus! {

///! This module implements an indexing calculus with corresponding lemmas. It only provides spec
///! functions, without any exec versions. The (specialized to specific entry_size) exec versions
///! can be implemented in their own modules and simply assert their equivalence to these spec
///! functions to make use of the lemmas. This is mainly because the absence of overflows may use
///! different bounds depending on the exact context. It also has the benefit that trusted exec
///! functions (e.g. in mem) are fully defined in their own modules


pub open spec fn nat_mul(a: nat, b: nat) -> nat {
    a * b
}

// This lemma has "support" postconditions for lemma_entry_base_from_index. I.e. postconditions
// that may help proving the lhs of some of that lemma's postconditions which are implications.
// However, one of these postconditions triggers on every multiplication, hence this is separated
// in its own lemma.
pub proof fn lemma_entry_base_from_index_support(base: nat, idx: nat, entry_size: nat)
    requires entry_size > 0
    ensures
        // forall|nested_es: nat, nested_num: nat|
        //     entry_size == nat_mul(nested_es, nested_num)
        //     ==> next_entry_base_from_index(base, idx, entry_size)
        //         == entry_base_from_index(entry_base_from_index(base, idx, entry_size), nested_num, nested_es),
        // Support postconditions:
        // Ugly, ugly workaround for mixed triggers.
        forall|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b),
        forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a),
        forall|a: nat| #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0 ==> aligned(base, entry_size),
{
    assert(forall|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b)) by(nonlinear_arith);
    assert(forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a)) by(nonlinear_arith);
    assert forall|a: nat|
        #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0
        implies
        aligned(base, entry_size) by
    {
        extra::mod_mult_zero_implies_mod_zero(base, entry_size, a);
    };
}

pub proof fn lemma_entry_base_from_index(base: nat, idx: nat, entry_size: nat)
    requires
        0 < entry_size,
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
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n),
        aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size),
        base <= entry_base_from_index(base, idx, entry_size),
        // forall|idx: nat, base: nat, layer: nat|
        //     layer < self.layers.len() && idx < self.num_entries(layer) ==> entry_base_from_index(base, idx, entry_size) < self.upper_vaddr(layer, base),
        // forall|idx: nat, base: nat, layer: nat|
            // layer < self.layers.len() && idx <= self.num_entries(layer) ==> entry_base_from_index(base, idx, entry_size) <= self.upper_vaddr(layer, base),
        // forall|idx: nat, base: nat, layer: nat|
            // layer + 1 < self.layers.len() ==> #[trigger] next_entry_base_from_index(base, idx, entry_size) == self.upper_vaddr(layer + 1, entry_base_from_index(base, idx, entry_size)),
        // // Support postconditions:
        // forall(|base: nat, n: nat| // Used to infer lhs of next postcondition's implication
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
                    0 < entry_size,
                    idx < idx2,
            {
                extra::mult_less_mono_both1(idx, entry_size, idx2, entry_size);
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
            0 < n && aligned(base, n) && aligned(entry_size, n)
            implies #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n) by
        {
            assert(aligned(entry_base_from_index(base, idx, entry_size), n))
                by(nonlinear_arith)
                requires
                    0 < n,
                    0 < entry_size,
                    aligned(base, n),
                    aligned(entry_size, n)
            {
                assert(aligned(idx * entry_size, entry_size)) by {
                    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(idx as int, entry_size as int);
                };
                assert(aligned(idx * entry_size, n)) by {
                    extra::aligned_transitive(idx * entry_size, entry_size, n);
                };
                assert(aligned(base + idx * entry_size, n)) by {
                    extra::mod_add_zero(base, idx * entry_size, n);
                };
            };
        };
        assert forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n)
            implies #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n) by
        {
            assert(aligned(next_entry_base_from_index(base, idx, entry_size), n))
                by(nonlinear_arith)
                requires
                    0 < n,
                    0 < entry_size,
                    aligned(base, n),
                    aligned(entry_size, n)
            {
                assert(aligned((idx + 1) * entry_size, entry_size)) by {
                    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(idx as int + 1, entry_size as int);
                };
                assert(aligned((idx + 1) * entry_size, n)) by {
                    extra::aligned_transitive((idx + 1) * entry_size, entry_size, n);
                };
                assert(aligned(base + (idx + 1) * entry_size, n)) by {
                    extra::mod_add_zero(base, (idx + 1) * entry_size, n);
                };
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
            &&& aligned(base, entry_size) && aligned(addr, entry_size) ==> addr == entry_base_from_index(base, idx, entry_size)
        }),
{
    let idx = index_from_base_and_addr(base, addr, entry_size);
    assert(idx < num_entries) by(nonlinear_arith)
        requires
            addr >= base,
            addr < entry_base_from_index(base, num_entries, entry_size),
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    { };
    assert(between(addr, entry_base_from_index(base, idx, entry_size), next_entry_base_from_index(base, idx, entry_size))) by(nonlinear_arith)
        requires
            addr >= base,
            addr < entry_base_from_index(base, num_entries, entry_size),
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    { };
    assert(aligned(base, entry_size) && aligned(addr, entry_size) ==> addr == entry_base_from_index(base, idx, entry_size)) by(nonlinear_arith)
        requires
            addr >= base,
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    {
        if aligned(base, entry_size) && aligned(addr, entry_size) {
            extra::subtract_mod_eq_zero(base, addr, entry_size);
            extra::div_mul_cancel(sub(addr, base), entry_size);
        }
    };
}
}
