#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use map::*;
use seq::*;
use set::*;
use set_lib::*;

use option::{ *, Option::* };
use crate::spec_t::{ hardware, hlspec };
use crate::impl_u::spec_pt;
use crate::definitions_t::{ between, MemRegion, overlap, PageTableEntry, RWOp, MapResult, UnmapResult, ResolveResult, Arch, aligned, new_seq, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem };
use crate::definitions_t::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE, WORD_SIZE };
use crate::spec_t::mem::{ word_index_spec };
use option::{ *, Option::* };
use crate::impl_u::{lib, indexing};
use crate::spec_t::os::*;

verus! {

pub proof fn lemma_pt_mappings_dont_overlap_in_pmem(this: OSVariables, other: OSVariables)
    requires
        this.pt_mappings_dont_overlap_in_pmem(),
        this.pt_entry_sizes_are_valid(),
        other.pt_entry_sizes_are_valid(),
        this.tlb_is_submap_of_pt(),
        other.tlb_is_submap_of_pt(),
    ensures
        forall|base, pte|
            !candidate_mapping_overlaps_existing_pmem(this.interp_pt_mem(), base, pte) &&
            other.interp_pt_mem() === this.interp_pt_mem().insert(base, pte)
            ==> other.pt_mappings_dont_overlap_in_pmem(),
        forall|base|
            other.interp_pt_mem() === this.interp_pt_mem().remove(base)
            ==> other.pt_mappings_dont_overlap_in_pmem(),
{
    assert forall|base, pte|
        !candidate_mapping_overlaps_existing_pmem(this.interp_pt_mem(), base, pte) &&
        other.interp_pt_mem() === this.interp_pt_mem().insert(base, pte)
        implies other.pt_mappings_dont_overlap_in_pmem() by
    {
        lemma_effective_mappings_equal_interp_pt_mem(this);
        lemma_effective_mappings_equal_interp_pt_mem(other);
        assert forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            other.interp_pt_mem().contains_pair(b1, pte1) && other.interp_pt_mem().contains_pair(b2, pte2)
            implies
            ((b1 == b2) || !overlap(pte1.frame, pte2.frame)) by
        {
            if b1 == b2 {
            } else {
                if b1 == base {
                    assert(!overlap(pte1.frame, pte2.frame));
                } else {
                    assert(this.interp_pt_mem().dom().contains(b1));
                    assert(this.interp_pt_mem().contains_pair(b1, pte1));
                    if b2 == base {
                        assert(pte2 === pte);
                        assert(!candidate_mapping_overlaps_existing_pmem(this.interp_pt_mem(), base, pte));
                        assert(forall|b: nat| {
                            this.interp_pt_mem().dom().contains(b)
                                ==> !(#[trigger] overlap(pte.frame, this.interp_pt_mem().index(b).frame))
                        });
                        assert(this.interp_pt_mem().index(b1) === pte1);
                        assert(this.interp_pt_mem().dom().contains(b1));
                        assert(!overlap(pte.frame, pte1.frame));
                        assert(pte.frame.size > 0);
                        assert(pte1.frame.size > 0);
                        assert(!overlap(pte1.frame, pte.frame));
                    } else {
                        assert(this.interp_pt_mem().dom().contains(b2));
                        assert(this.interp_pt_mem().contains_pair(b2, pte2));
                        assert(!overlap(pte1.frame, pte2.frame));
                    }
                }
            }
        };
    };
    assert forall|base|
        other.interp_pt_mem() === this.interp_pt_mem().remove(base)
        implies
        other.pt_mappings_dont_overlap_in_pmem() by
    {
        lemma_effective_mappings_equal_interp_pt_mem(this);
        lemma_effective_mappings_equal_interp_pt_mem(other);
        assert forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            other.interp_pt_mem().contains_pair(b1, pte1) && other.interp_pt_mem().contains_pair(b2, pte2)
            implies
            ((b1 == b2) || !overlap(pte1.frame, pte2.frame)) by
        {
            if b1 == b2 {
            } else {
                assert(b2 != base);
                if b1 == base {
                    assert(!overlap(pte1.frame, pte2.frame));
                } else {
                    assert(this.interp_pt_mem().dom().contains(b1));
                    assert(this.interp_pt_mem().contains_pair(b1, pte1));
                    assert(this.interp_pt_mem().dom().contains(b2));
                    assert(this.interp_pt_mem().contains_pair(b2, pte2));
                    assert(!overlap(pte1.frame, pte2.frame));
                }
            }
        };

    };
}

pub proof fn lemma_effective_mappings_equal_interp_pt_mem(this: OSVariables)
    requires
        this.tlb_is_submap_of_pt()
    ensures
        this.effective_mappings() === this.interp_pt_mem(),
{
    let eff = this.effective_mappings();
    let pt  = this.interp_pt_mem();
    let tlb = this.hw.tlb;
    assert forall|base|
        eff.dom().contains(base)
        implies pt.dom().contains(base) by
    { assert(pt.contains_pair(base, eff.index(base))); };
    assert forall|base|
        pt.dom().contains(base)
        implies eff.dom().contains(base) by
    {
        if tlb.dom().contains(base) {
            if tlb.index(base) !== pt.index(base) {
                let pteprime = tlb.index(base);
                assert(pt.contains_pair(base, pteprime));
                assert(false);
            }
            assert(eff.contains_pair(base, pt.index(base)));
        } else {
            assert(eff.contains_pair(base, pt.index(base)));
        }
    };
    assert forall|base|
        eff.dom().contains(base) && pt.dom().contains(base)
        implies #[trigger] pt.index(base) === #[trigger] eff.index(base) by
    {
        let pte = eff.index(base);
        assert(eff.contains_pair(base, pte));
        assert(pt.contains_pair(base, pte));
    };
    lib::assert_maps_equal_contains_pair::<nat,PageTableEntry>(eff, pt);
}

pub proof fn lemma_effective_mappings_other(this: OSVariables, other: OSVariables)
    requires
        this.tlb_is_submap_of_pt(),
        other.tlb_is_submap_of_pt(),
        this.hw.pt_mem === other.hw.pt_mem,
    ensures
        this.effective_mappings() === other.effective_mappings(),
{
    let eff1 = this.effective_mappings();
    let eff2 = other.effective_mappings();
    let tlb1 = this.hw.tlb;
    let tlb2 = other.hw.tlb;
    let pt1 = this.interp_pt_mem();
    let pt2 = other.interp_pt_mem();
    assert forall|base, pte|
        eff1.contains_pair(base, pte)
        implies eff2.contains_pair(base, pte) by
    {
        assert(pt1.contains_pair(base, pte));
        assert(pt2.contains_pair(base, pte));
        if tlb2.dom().contains(base) {
            if tlb2.index(base) !== pte {
                let pteprime = tlb2.index(base);
                assert(pt2.contains_pair(base, pteprime));
                assert(false);
            }
            assert(tlb2.contains_pair(base, pte));
            assert(eff2.contains_pair(base, pte));
        } else {
            assert(eff2.contains_pair(base, pte));
        }
        assert(eff2.contains_pair(base, pte));
    };
    assert forall|base, pte|
        eff2.contains_pair(base, pte)
        implies eff1.contains_pair(base, pte) by
    {
        assert(pt1.contains_pair(base, pte));
        assert(pt2.contains_pair(base, pte));
        if tlb1.dom().contains(base) {
            if tlb1.index(base) !== pte {
                let pteprime = tlb1.index(base);
                assert(pt1.contains_pair(base, pteprime));
                assert(false);
            }
            assert(tlb1.contains_pair(base, pte));
            assert(eff1.contains_pair(base, pte));
        } else {
            assert(eff1.contains_pair(base, pte));
        }
        assert(eff1.contains_pair(base, pte));
    };
    lib::assert_maps_equal_contains_pair::<nat,PageTableEntry>(eff1, eff2);
}

proof fn lemma_interp(this: OSVariables)
    requires
        this.inv()
    ensures
        this.interp().mappings === this.interp_pt_mem(),
        this.interp().mappings === this.effective_mappings(),
        forall|base: nat, pte: PageTableEntry, vmem_idx: nat| {
            let vaddr = vmem_idx * WORD_SIZE as nat;
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            #[trigger] this.interp_pt_mem().contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size) && pmem_idx < this.hw.mem.len()
            ==> this.hw.mem.index(pmem_idx) === #[trigger] this.interp().mem.index(vmem_idx)
        },
{
    lemma_effective_mappings_equal_interp_pt_mem(this);
    assert forall|base: nat, pte: PageTableEntry, vmem_idx: nat| {
        let vaddr = vmem_idx * WORD_SIZE as nat;
        let paddr = (pte.frame.base + (vaddr - base)) as nat;
        let pmem_idx = word_index_spec(paddr);
        #[trigger] this.interp_pt_mem().contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size) && pmem_idx < this.hw.mem.len()
    } implies this.hw.mem.index(word_index_spec((pte.frame.base + ((vmem_idx * WORD_SIZE as nat) - base)) as nat)) === #[trigger] this.interp().mem.index(vmem_idx)
    by {
        let pt = this.interp_pt_mem();
        let sys_mem = this.hw.mem;
        let vaddr = vmem_idx * WORD_SIZE as nat;
        let paddr = (pte.frame.base + (vaddr - base)) as nat;
        let pmem_idx = word_index_spec(paddr);
        if this.hw.mem.index(pmem_idx) !== this.interp().mem.index(vmem_idx) {
            assert(exists|base, pte| pt.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size));
            let (base2, pte2): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] pt.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            if base2 == base {
                assert(pte2 === pte);
                assert(false);
            } else {
                assert(overlap(
                        MemRegion { base: base,  size: pte.frame.size },
                        MemRegion { base: base2, size: pte2.frame.size }));
                assert(false);
            }
        }
    }
}

proof fn lemma_interp_other(this: OSVariables, other: OSVariables)
    requires
        other.hw.mem === this.hw.mem,
        forall|base, pte| this.effective_mappings().contains_pair(base, pte) ==> other.effective_mappings().contains_pair(base, pte),
        this.inv(),
        other.inv(),
    ensures
        forall|word_idx: nat|
            this.interp().mem.dom().contains(word_idx)
            ==> {
                &&& other.interp().mem.dom().contains(word_idx)
                &&& #[trigger] other.interp().mem.index(word_idx) == #[trigger] this.interp().mem.index(word_idx)
            },
{
    assert forall|word_idx: nat|
        this.interp().mem.dom().contains(word_idx)
        implies {
            &&& other.interp().mem.dom().contains(word_idx)
            &&& #[trigger] other.interp().mem.index(word_idx) == #[trigger] this.interp().mem.index(word_idx)
        } by
    {
        let vaddr = word_idx * WORD_SIZE as nat;
        let this_mappings = this.effective_mappings();
        let other_mappings = other.effective_mappings();
        let phys_mem_size = this.interp_constants().phys_mem_size;
        assert(hlspec::mem_domain_from_mappings_contains(phys_mem_size, word_idx, this_mappings));
        let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] this_mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
        assert(this_mappings.contains_pair(base, pte));
        assert(between(vaddr, base, base + pte.frame.size));
        assert(other_mappings.contains_pair(base, pte));

        assert(other.interp().mem.dom().contains(word_idx));
        if other.interp().mem[word_idx] !== this.interp().mem[word_idx] {
            let (base2, pte2): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] other_mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            assert(other_mappings.contains_pair(base, pte));
            assert(other_mappings.contains_pair(base2, pte2));
            assert(between(vaddr, base2, base2 + pte2.frame.size));
            assert(overlap(
                    MemRegion { base: base, size: base + pte.frame.size },
                    MemRegion { base: base2, size: base2 + pte2.frame.size }));
            assert(other.pt_mappings_dont_overlap_in_vmem());
            assert(((base == base2) || !overlap(
                           MemRegion { base: base, size: pte.frame.size },
                           MemRegion { base: base2, size: pte2.frame.size })));
            assert(base != base2);
            assert(false);
        }
    };
}

// not technically necessary, i think
proof fn init_implies_pt_init(s: OSVariables)
    requires
        init(s)
    ensures
        spec_pt::init(s.pt_variables());

proof fn init_implies_inv(s: OSVariables)
    requires
        init(s)
    ensures
        s.inv()
{
    reveal(OSVariables::pt_entries_aligned);
}

proof fn next_step_preserves_inv(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step)
    ensures
        s2.inv(),
{
    reveal(OSVariables::pt_entries_aligned);
    match step {
        OSStep::HW { step: system_step } => {
            assert(step_HW(s1, s2, system_step));
        },
        OSStep::Map { vaddr, pte, result } => {
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(step_Map(s1, s2, vaddr, pte, result));
            assert(spec_pt::step_Map(pt_s1, pt_s2, vaddr, pte, result));
            assert(!candidate_mapping_overlaps_existing_pmem(pt_s1.map, vaddr, pte));
            if candidate_mapping_overlaps_existing_vmem(pt_s1.map, vaddr, pte) {
                assert(s2.inv());
            } else {
                assert(forall|base, pte| s1.interp_pt_mem().contains_pair(base, pte) ==> s2.interp_pt_mem().contains_pair(base, pte));
                assert forall|base, pteprime| s2.interp_pt_mem().contains_pair(base, pteprime) implies {
                    ||| pteprime.frame.size == L3_ENTRY_SIZE
                    ||| pteprime.frame.size == L2_ENTRY_SIZE
                    ||| pteprime.frame.size == L1_ENTRY_SIZE
                } by
                {
                    if vaddr == base {
                        assert({
                            ||| pteprime.frame.size == L3_ENTRY_SIZE
                            ||| pteprime.frame.size == L2_ENTRY_SIZE
                            ||| pteprime.frame.size == L1_ENTRY_SIZE
                        });
                    } else {
                        assert(s1.pt_entry_sizes_are_valid());
                        assert(s1.interp_pt_mem().dom().contains(base));
                        assert(s1.interp_pt_mem().contains_pair(base, pteprime));
                        assert({
                            ||| pteprime.frame.size == L3_ENTRY_SIZE
                            ||| pteprime.frame.size == L2_ENTRY_SIZE
                            ||| pteprime.frame.size == L1_ENTRY_SIZE
                        });
                    }
                };
                assert(s2.pt_entry_sizes_are_valid());
                assert(s2.tlb_is_submap_of_pt());
                lemma_pt_mappings_dont_overlap_in_pmem(s1, s2);
                assert(s2.pt_mappings_dont_overlap_in_pmem());
                assert(s2.pt_entries_aligned()) by {
                    assert forall|base2, pte2|
                        s2.interp_pt_mem().contains_pair(base2, pte2)
                        implies
                        aligned(base2, 8) && aligned(pte2.frame.base, 8) by
                    {
                        if base2 === vaddr {
                            assert(pte2 === pte);
                            assert(aligned(vaddr, pte.frame.size));
                            assert(aligned(pte.frame.base, pte.frame.size));
                            if pte.frame.size == L3_ENTRY_SIZE {
                                lib::aligned_transitive(pte.frame.base, L3_ENTRY_SIZE, 8);
                                lib::aligned_transitive(vaddr, L3_ENTRY_SIZE, 8);
                                assert(aligned(vaddr, 8));
                                assert(aligned(pte.frame.base, 8));
                            } else if pte.frame.size == L2_ENTRY_SIZE {
                                lib::aligned_transitive(pte.frame.base, L2_ENTRY_SIZE, 8);
                                lib::aligned_transitive(vaddr, L2_ENTRY_SIZE, 8);
                                assert(aligned(vaddr, 8));
                                assert(aligned(pte.frame.base, 8));
                            } else {
                                assert(pte.frame.size == L1_ENTRY_SIZE);
                                assert(aligned(L1_ENTRY_SIZE, 8));
                                lib::aligned_transitive(pte.frame.base, L1_ENTRY_SIZE, 8);
                                lib::aligned_transitive(vaddr, L1_ENTRY_SIZE, 8);
                                assert(aligned(vaddr, 8));
                                assert(aligned(pte.frame.base, 8));
                            }
                        } else {
                            assert(s1.interp_pt_mem().contains_pair(base2, pte2));
                        }
                    };
                };
                assert(s2.inv());
            }
        },
        OSStep::Unmap { vaddr, result } => {
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(step_Unmap(s1, s2, vaddr, result));
            assert(spec_pt::step_Unmap(pt_s1, pt_s2, vaddr, result));
            if pt_s1.map.dom().contains(vaddr) {
                assert(result.is_Ok());
                assert(pt_s2.map === pt_s1.map.remove(vaddr));
                // assert(s2.pt_mappings_dont_overlap_in_vmem());
                assert forall|base2, pte2|
                    s2.hw.tlb.contains_pair(base2, pte2)
                    implies #[trigger] s2.interp_pt_mem().contains_pair(base2, pte2) by
                {
                    assert(s1.hw.tlb.contains_pair(base2, pte2));
                    assert(s1.tlb_is_submap_of_pt());
                    assert(s1.interp_pt_mem().contains_pair(base2, pte2));
                    assert(s2.interp_pt_mem().contains_pair(base2, pte2));
                };
                assert forall|baseprime, pteprime| s2.interp_pt_mem().contains_pair(baseprime, pteprime) implies {
                    ||| pteprime.frame.size == L3_ENTRY_SIZE
                    ||| pteprime.frame.size == L2_ENTRY_SIZE
                    ||| pteprime.frame.size == L1_ENTRY_SIZE
                } by
                {
                    assert(s1.pt_entry_sizes_are_valid());
                    assert(s1.interp_pt_mem().dom().contains(baseprime));
                    assert(s1.interp_pt_mem().contains_pair(baseprime, pteprime));
                    assert({
                        ||| pteprime.frame.size == L3_ENTRY_SIZE
                        ||| pteprime.frame.size == L2_ENTRY_SIZE
                        ||| pteprime.frame.size == L1_ENTRY_SIZE
                    });
                };
                assert(s2.pt_entry_sizes_are_valid());
                lemma_pt_mappings_dont_overlap_in_pmem(s1, s2);
                assert(s2.pt_entries_aligned()) by {
                    assert forall|base, pte|
                        s2.interp_pt_mem().contains_pair(base, pte)
                        implies
                        aligned(base, 8) && aligned(pte.frame.base, 8) by
                    { assert(s1.interp_pt_mem().contains_pair(base, pte)); };
                };
                assert(s2.inv());
            } else {
                assert(s2.inv());
            }
        },
        OSStep::Resolve { vaddr, result } => (),
    }
}

proof fn init_refines_hl_init(s: OSVariables)
    requires
        init(s)
    ensures
        hlspec::init(s.interp())
{
    lemma_effective_mappings_equal_interp_pt_mem(s);
    assert_maps_equal!(s.interp().mem, Map::empty());
}

proof fn next_step_refines_hl_next_step(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step)
    ensures
        hlspec::next_step(s1.interp_constants(), s1.interp(), s2.interp(), step.interp())
{
    next_step_preserves_inv(s1, s2, step);
    lemma_effective_mappings_equal_interp_pt_mem(s1);
    lemma_effective_mappings_equal_interp_pt_mem(s2);
    let abs_s1   = s1.interp();
    let abs_s2   = s2.interp();
    let abs_c    = s1.interp_constants();
    let sys_s1   = s1.hw;
    let sys_s2   = s2.hw;
    let pt1      = s1.interp_pt_mem();
    let pt2      = s2.interp_pt_mem();
    let abs_step = step.interp();
    match step {
        OSStep::HW { step: system_step } => {
            lemma_effective_mappings_other(s1, s2);
            match system_step {
                hardware::HWStep::ReadWrite { vaddr, paddr, op, pte } => {
                    // hlspec::AbstractStep::ReadWrite { vaddr, op, pte }
                    let pmem_idx = word_index_spec(paddr);
                    let vmem_idx = word_index_spec(vaddr);
                    assert(sys_s2.pt_mem === sys_s1.pt_mem);
                    assert(sys_s2.tlb === sys_s1.tlb);
                    match pte {
                        Some((base, pte)) => {
                            lemma_interp(s1);
                            lemma_interp(s2);

                            // hw
                            assert(sys_s1.tlb.contains_pair(base, pte));
                            assert(between(vaddr, base, base + pte.frame.size));
                            assert(paddr === (pte.frame.base + (vaddr - base)) as nat);

                            // abs
                            assert(abs_s1.mappings.contains_pair(base, pte));
                            match op {
                                RWOp::Store { new_value, result } => {
                                    if pmem_idx < sys_s1.mem.len() && !pte.flags.is_supervisor && pte.flags.is_writable {
                                        assert(result.is_Ok());
                                        assert(sys_s2.mem === sys_s1.mem.update(pmem_idx, new_value));
                                        assert(hlspec::mem_domain_from_mappings_contains(abs_c.phys_mem_size, vmem_idx, s1.interp_pt_mem()));
                                        assert(abs_s1.mem.dom() === abs_s2.mem.dom());

                                        assert(sys_s1.mem.index(pmem_idx) == abs_s1.mem.index(vmem_idx));

                                        assert(abs_s1.mem.dom().contains(vmem_idx));
                                        assert(abs_s1.mem.insert(vmem_idx, new_value).dom() === abs_s1.mem.dom().insert(vmem_idx));
                                        assert_sets_equal!(abs_s1.mem.dom(), abs_s1.mem.dom().insert(vmem_idx));
                                        assert(abs_s1.mem.insert(vmem_idx, new_value).dom() === abs_s2.mem.dom());
                                        assert forall|vmem_idx2: nat|
                                            abs_s2.mem.dom().contains(vmem_idx2) &&
                                            abs_s1.mem.insert(vmem_idx, new_value).dom().contains(vmem_idx2)
                                            implies
                                            #[trigger] abs_s2.mem.index(vmem_idx2) == abs_s1.mem.insert(vmem_idx, new_value).index(vmem_idx2) by
                                        {
                                            if vmem_idx2 == vmem_idx {
                                                assert(abs_s2.mem.index(vmem_idx2) == new_value);
                                            } else {
                                                assert(hlspec::mem_domain_from_mappings_contains(abs_c.phys_mem_size, vmem_idx2, pt1));
                                                let vaddr2 = vmem_idx2 * WORD_SIZE as nat;
                                                let (base2, pte2): (nat, PageTableEntry) = choose|base2: nat, pte2: PageTableEntry| {
                                                    let paddr2 = (pte2.frame.base + (vaddr2 - base2)) as nat;
                                                    let pmem_idx2 = word_index_spec(paddr2);
                                                    &&& #[trigger] pt1.contains_pair(base2, pte2)
                                                    &&& between(vaddr2, base2, base2 + pte2.frame.size)
                                                    &&& pmem_idx2 < abs_c.phys_mem_size
                                                };
                                                let paddr2 = (pte2.frame.base + (vaddr2 - base2)) as nat;
                                                let pmem_idx2 = word_index_spec(paddr2);
                                                assert(pt1.contains_pair(base2, pte2));
                                                assert(between(vaddr2, base2, base2 + pte2.frame.size));
                                                assert(pmem_idx2 < abs_c.phys_mem_size);
                                                assert(abs_s1.mem.index(vmem_idx2) == s1.hw.mem.index(pmem_idx2));
                                                assert(abs_s2.mem.index(vmem_idx2) == s2.hw.mem.index(pmem_idx2));
                                                assert(s2.hw.mem === s1.hw.mem.update(pmem_idx, new_value));
                                                assert(pmem_idx < s1.hw.mem.len());
                                                assert(pmem_idx2 < s1.hw.mem.len());
                                                lib::mod_of_mul(vmem_idx2, WORD_SIZE);
                                                assert(aligned(paddr, 8)) by {
                                                    reveal(OSVariables::pt_entries_aligned);
                                                    assert(aligned(pte.frame.base, 8));
                                                    assert(aligned(base, 8));
                                                    assert(aligned(vaddr, 8));
                                                    lib::subtract_mod_eq_zero(base, vaddr, 8);
                                                    lib::mod_add_zero(pte.frame.base, sub(vaddr, base), 8);
                                                };
                                                assert(aligned(paddr2, 8)) by {
                                                    reveal(OSVariables::pt_entries_aligned);
                                                    assert(aligned(pte2.frame.base, 8));
                                                    assert(aligned(base2, 8));
                                                    assert(aligned(vaddr2, 8));
                                                    lib::subtract_mod_eq_zero(base2, vaddr2, 8);
                                                    lib::mod_add_zero(pte2.frame.base, sub(vaddr2, base2), 8);
                                                };
                                                if pmem_idx == pmem_idx2 {
                                                    assert(vaddr != vaddr2);
                                                    assert(pte === pte2);
                                                    assert(vaddr - base != vaddr2 - base);
                                                    assert(paddr != paddr2);
                                                    assert(paddr  == (pte.frame.base + (vaddr - base)) as nat);
                                                    assert(paddr2 == (pte2.frame.base + (vaddr2 - base2)) as nat);
                                                    assert(false);
                                                }
                                                assert(s1.hw.mem.index(pmem_idx2) == s2.hw.mem.index(pmem_idx2));

                                                assert(abs_s2.mem.index(vmem_idx2) == abs_s1.mem.index(vmem_idx2));
                                            }
                                        };
                                        assert_maps_equal!(abs_s2.mem, abs_s1.mem.insert(vmem_idx, new_value));
                                        assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(sys_s2.mem === sys_s1.mem);
                                        assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    }
                                },
                                RWOp::Load { is_exec, result } => {
                                    assert(sys_s2.mem === sys_s1.mem);
                                    if pmem_idx < sys_s1.mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                                        assert(result.is_Value());
                                        assert(result.get_Value_0() == sys_s1.mem.index(pmem_idx));
                                        assert(hlspec::mem_domain_from_mappings_contains(abs_c.phys_mem_size, vmem_idx, s1.interp_pt_mem()));
                                        assert(sys_s1.mem.index(pmem_idx) == abs_s1.mem.index(vmem_idx));
                                        assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    }
                                },
                            }
                        },
                        None => {
                            assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, pte));
                        },
                    }
                    assert(hlspec::step_ReadWrite(abs_c, abs_s1, abs_s2, vaddr, op, pte));
                    assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
                },
                hardware::HWStep::PTMemOp => assert(false),
                hardware::HWStep::TLBFill { vaddr, pte } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
                hardware::HWStep::TLBEvict { vaddr } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
            }
        },
        OSStep::Map { vaddr, pte, result } => {
            // hlspec::AbstractStep::Map { vaddr, pte }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Map { vaddr, pte, result });
            assert(step_Map(s1, s2, vaddr, pte, result));
            assert(spec_pt::step_Map(pt_s1, pt_s2, vaddr, pte, result));
            assert(hlspec::step_Map_enabled(abs_s1.mappings, vaddr, pte));
            if candidate_mapping_overlaps_existing_vmem(pt_s1.map, vaddr, pte) {
                assert(candidate_mapping_overlaps_existing_vmem(abs_s1.mappings, vaddr, pte));
                assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            } else {
                assert(!candidate_mapping_overlaps_existing_vmem(abs_s1.mappings, vaddr, pte));
                assert(forall|base, pte| s1.interp_pt_mem().contains_pair(base, pte) ==> s2.interp_pt_mem().contains_pair(base, pte));
                assert(forall|base, pte| s1.interp().mappings.contains_pair(base, pte) ==> s2.interp().mappings.contains_pair(base, pte));
                assert(s1.interp().mappings === s1.interp_pt_mem());
                assert(s2.interp().mappings === s2.interp_pt_mem());
                lemma_interp_other(s1, s2);
                assert(result.is_Ok());
                assert(abs_s2.mappings === abs_s1.mappings.insert(vaddr, pte));
                assert forall|word_idx|
                    #[trigger] abs_s1.mem.dom().contains(word_idx)
                    implies abs_s2.mem[word_idx] === abs_s1.mem[word_idx] by
                {
                    assert(abs_s2.mem.dom().contains(word_idx));
                    assert(abs_s2.mem[word_idx] == abs_s1.mem[word_idx]);
                };
                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(abs_c.phys_mem_size, abs_s2.mappings));
                assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            }
            assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
        },
        OSStep::Unmap { vaddr, result } => {
            // hlspec::AbstractStep::Unmap { vaddr }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Unmap { vaddr, result });
            assert(step_Unmap(s1, s2, vaddr, result));
            assert(spec_pt::step_Unmap(pt_s1, pt_s2, vaddr, result));
            assert(hlspec::step_Unmap_enabled(vaddr));
            if pt_s1.map.dom().contains(vaddr) {
                assert(abs_s1.mappings.dom().contains(vaddr));
                assert(result.is_Ok());
                assert(pt_s2.map === pt_s1.map.remove(vaddr));
                assert(abs_s2.mappings === abs_s1.mappings.remove(vaddr));

                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(abs_c.phys_mem_size, abs_s2.mappings));
                lemma_interp_other(s2, s1);
                assert forall|word_idx|
                    #[trigger] abs_s2.mem.dom().contains(word_idx)
                    implies abs_s1.mem[word_idx] === abs_s2.mem[word_idx] by
                {
                    assert(abs_s1.mem[word_idx] == abs_s2.mem[word_idx]);
                };

                assert(hlspec::step_Unmap(abs_c, abs_s1, abs_s2, vaddr, result));
            } else {
                assert(!abs_s1.mappings.dom().contains(vaddr));
                assert(hlspec::step_Unmap(abs_c, abs_s1, abs_s2, vaddr, result));
            }
            assert(hlspec::step_Unmap(abs_c, abs_s1, abs_s2, vaddr, result));
            assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
        },
        OSStep::Resolve { vaddr, result } => {
            // hlspec::AbstractStep::Resolve { vaddr, result }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Resolve { vaddr, result });
            assert(step_Resolve(s1, s2, vaddr, result));
            assert(spec_pt::step_Resolve(pt_s1, pt_s2, vaddr, result));
            match result {
                ResolveResult::Ok(base, pte) => {
                    assert(hlspec::step_Resolve(abs_c, abs_s1, abs_s2, vaddr, ResolveResult::Ok(base, pte)));
                },
                ResolveResult::ErrUnmapped => {
                    let vmem_idx = word_index_spec(vaddr);
                    assert(vmem_idx * WORD_SIZE == vaddr);
                    if hlspec::mem_domain_from_mappings(abs_c.phys_mem_size, abs_s1.mappings).contains(vmem_idx) {
                        assert(hlspec::mem_domain_from_mappings_contains(abs_c.phys_mem_size, vmem_idx, abs_s1.mappings));
                        let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| {
                            let paddr = (pte.frame.base + (vaddr - base)) as nat;
                            let pmem_idx = word_index_spec(paddr);
                            &&& #[trigger] abs_s1.mappings.contains_pair(base, pte)
                            &&& between(vaddr, base, base + pte.frame.size)
                            &&& pmem_idx < abs_c.phys_mem_size
                        };
                        assert(pt_s1.map.contains_pair(base, pte));
                        assert(false);
                    }
                    assert(hlspec::step_Resolve(abs_c, abs_s1, abs_s2, vaddr, result));
                },
            }
            assert(hlspec::step_Resolve(abs_c, abs_s1, abs_s2, vaddr, result));
            assert(hlspec::next_step(abs_c, abs_s1, abs_s2, abs_step));
        },
    }
}

}
