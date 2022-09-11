#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use map::*;
use seq::*;
use set_lib::*;

use crate::spec_t::{ hardware, hlspec };
use crate::impl_u::spec_pt;
use crate::definitions_t::{ between, MemRegion, overlap, PageTableEntry, IoOp, MapResult, UnmapResult, Arch, aligned, new_seq, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem };
use crate::definitions_t::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE, WORD_SIZE };
use crate::mem_t::{ word_index_spec };
use option::{ *, Option::* };

verus! {

pub proof fn assert_maps_equal_contains_pair<K,V>(m1: Map<K,V>, m2: Map<K,V>)
    requires
        forall|k:K,v:V| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k:K,v:V| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2
{
    assert forall|k|
        m1.dom().contains(k)
        implies m2.dom().contains(k) by
    { assert(m2.contains_pair(k, m1.index(k))); };
    assert forall|k|
        m2.dom().contains(k)
        implies m1.dom().contains(k) by
    { assert(m1.contains_pair(k, m2.index(k))); };
    assert forall|k|
        m1.dom().contains(k) && m2.dom().contains(k)
        implies #[trigger] m2.index(k) === #[trigger] m1.index(k) by
    {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    };
    assert_maps_equal!(m1, m2);
}

pub struct OSVariables {
    pub system: hardware::HWVariables,
}

impl OSVariables {
    pub open spec fn pt_mappings_dont_overlap_in_vmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: pte1.frame.size },
                    MemRegion { base: b2, size: pte2.frame.size }))
    }

    pub open spec fn pt_mappings_dont_overlap_in_pmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(pte1.frame, pte2.frame))
    }

    pub proof fn lemma_pt_mappings_dont_overlap_in_pmem(self, other: Self)
        requires
            self.pt_mappings_dont_overlap_in_pmem(),
            self.pt_entry_sizes_are_valid(),
            other.pt_entry_sizes_are_valid(),
            self.tlb_is_submap_of_pt(),
            other.tlb_is_submap_of_pt(),
        ensures
            forall|base, pte|
                !candidate_mapping_overlaps_existing_pmem(self.interp_pt_mem(), base, pte) &&
                other.interp_pt_mem() === self.interp_pt_mem().insert(base, pte)
                ==> other.pt_mappings_dont_overlap_in_pmem(),
            forall|base|
                other.interp_pt_mem() === self.interp_pt_mem().remove(base)
                ==> other.pt_mappings_dont_overlap_in_pmem(),
    {
        assert forall|base, pte|
            !candidate_mapping_overlaps_existing_pmem(self.interp_pt_mem(), base, pte) &&
            other.interp_pt_mem() === self.interp_pt_mem().insert(base, pte)
            implies other.pt_mappings_dont_overlap_in_pmem() by
        {
            self.lemma_effective_mappings_equal_interp_pt_mem();
            other.lemma_effective_mappings_equal_interp_pt_mem();
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
                        assert(self.interp_pt_mem().dom().contains(b1));
                        assert(self.interp_pt_mem().contains_pair(b1, pte1));
                        if b2 == base {
                            assert(pte2 === pte);
                            assert(!candidate_mapping_overlaps_existing_pmem(self.interp_pt_mem(), base, pte));
                            assert(forall|b: nat| {
                                self.interp_pt_mem().dom().contains(b)
                                    ==> !(#[trigger] overlap(pte.frame, self.interp_pt_mem().index(b).frame))
                            });
                            assert(self.interp_pt_mem().index(b1) === pte1);
                            assert(self.interp_pt_mem().dom().contains(b1));
                            assert(!overlap(pte.frame, pte1.frame));
                            assert(pte.frame.size > 0);
                            assert(pte1.frame.size > 0);
                            assert(!overlap(pte1.frame, pte.frame));
                        } else {
                            assert(self.interp_pt_mem().dom().contains(b2));
                            assert(self.interp_pt_mem().contains_pair(b2, pte2));
                            assert(!overlap(pte1.frame, pte2.frame));
                        }
                    }
                }
            };
        };
        assert forall|base|
            other.interp_pt_mem() === self.interp_pt_mem().remove(base)
            implies
            other.pt_mappings_dont_overlap_in_pmem() by
        {
            self.lemma_effective_mappings_equal_interp_pt_mem();
            other.lemma_effective_mappings_equal_interp_pt_mem();
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
                        assert(self.interp_pt_mem().dom().contains(b1));
                        assert(self.interp_pt_mem().contains_pair(b1, pte1));
                        assert(self.interp_pt_mem().dom().contains(b2));
                        assert(self.interp_pt_mem().contains_pair(b2, pte2));
                        assert(!overlap(pte1.frame, pte2.frame));
                    }
                }
            };

        };
    }

    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, pte| self.system.tlb.contains_pair(base, pte) ==> #[trigger] self.interp_pt_mem().contains_pair(base, pte)
    }

    pub open spec fn pt_entry_sizes_are_valid(self) -> bool {
        forall|base, pte| self.interp_pt_mem().contains_pair(base, pte) ==> {
            ||| pte.frame.size == L3_ENTRY_SIZE
            ||| pte.frame.size == L2_ENTRY_SIZE
            ||| pte.frame.size == L1_ENTRY_SIZE
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.pt_mappings_dont_overlap_in_vmem()
        &&& self.pt_mappings_dont_overlap_in_pmem()
        &&& self.pt_entry_sizes_are_valid()
        &&& self.tlb_is_submap_of_pt()
    }

    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables {
            map: self.interp_pt_mem(),
        }
    }

    pub open spec fn interp_pt_mem(self) -> Map<nat,PageTableEntry> {
        hardware::interp_pt_mem(self.system.pt_mem)
    }

    pub open spec fn effective_mappings(self) -> Map<nat,PageTableEntry> {
        Map::new(
            |base: nat| self.system.tlb.dom().contains(base) || self.interp_pt_mem().dom().contains(base),
            |base: nat| if self.system.tlb.dom().contains(base) { self.system.tlb.index(base) } else { self.interp_pt_mem().index(base) },
            )
    }

    pub proof fn lemma_effective_mappings_equal_interp_pt_mem(self)
        requires
            self.tlb_is_submap_of_pt()
        ensures
            self.effective_mappings() === self.interp_pt_mem(),
    {
        let eff = self.effective_mappings();
        let pt  = self.interp_pt_mem();
        let tlb = self.system.tlb;
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
        assert_maps_equal_contains_pair::<nat,PageTableEntry>(eff, pt);
    }

    pub proof fn lemma_effective_mappings_other(self, other: Self)
        requires
            self.tlb_is_submap_of_pt(),
            other.tlb_is_submap_of_pt(),
            self.system.pt_mem === other.system.pt_mem,
        ensures
            self.effective_mappings() === other.effective_mappings(),
    {
        let eff1 = self.effective_mappings();
        let eff2 = other.effective_mappings();
        let tlb1 = self.system.tlb;
        let tlb2 = other.system.tlb;
        let pt1 = self.interp_pt_mem();
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
        assert_maps_equal_contains_pair::<nat,PageTableEntry>(eff1, eff2);
    }

    pub open spec fn interp_vmem(self) -> Map<nat,nat> {
        let phys_mem_size = self.interp_constants().phys_mem_size;
        let mappings: Map<nat,PageTableEntry> = self.effective_mappings();
        Map::new(
            |vmem_idx: nat| hlspec::mem_domain_from_mappings_contains(phys_mem_size, vmem_idx, mappings),
            |vmem_idx: nat| {
                let vaddr = vmem_idx * WORD_SIZE as nat;
                let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = word_index_spec(paddr);
                self.system.mem[pmem_idx]
            })
    }

    pub open spec fn interp(self) -> hlspec::AbstractVariables {
        let mappings: Map<nat,PageTableEntry> = self.effective_mappings();
        let mem: Map<nat,nat> = self.interp_vmem();
        hlspec::AbstractVariables {
            mem,
            mappings,
        }
    }

    pub open spec fn interp_constants(self) -> hlspec::AbstractConstants {
        hlspec::AbstractConstants {
            phys_mem_size: self.system.mem.len(),
        }
    }

    pub proof fn lemma_interp_manual(self, base: nat, pte: PageTableEntry, vmem_idx: nat)
        requires
            self.inv(),
            self.interp_pt_mem().contains_pair(base, pte),
            between(vmem_idx * WORD_SIZE as nat, base, base + pte.frame.size),
            word_index_spec((pte.frame.base + ((vmem_idx * WORD_SIZE as nat) - base)) as nat) < self.system.mem.len()
        ensures
            self.interp().mappings === self.interp_pt_mem(),
            self.interp().mappings === self.effective_mappings(),
            ({
                let vaddr = vmem_idx * WORD_SIZE as nat;
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = word_index_spec(paddr);
                &&& self.interp().mem.dom().contains(vmem_idx)
                &&& self.interp().mem.index(vmem_idx) == self.system.mem.index(pmem_idx)
                &&& self.interp().mem.contains_pair(vmem_idx, self.system.mem.index(pmem_idx))
            })
    {
        self.lemma_interp();
    }

    proof fn lemma_interp(self)
        requires
            self.inv()
        ensures
            self.interp().mappings === self.interp_pt_mem(),
            self.interp().mappings === self.effective_mappings(),
            forall|base: nat, pte: PageTableEntry, vmem_idx: nat| {
                let vaddr = vmem_idx * WORD_SIZE as nat;
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = word_index_spec(paddr);
                #[trigger] self.interp_pt_mem().contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size) && pmem_idx < self.system.mem.len()
                ==> self.system.mem.index(pmem_idx) === #[trigger] self.interp().mem.index(vmem_idx)
            },
    {
        self.lemma_effective_mappings_equal_interp_pt_mem();
        assert forall|base: nat, pte: PageTableEntry, vmem_idx: nat| {
            let vaddr = vmem_idx * WORD_SIZE as nat;
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            #[trigger] self.interp_pt_mem().contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size) && pmem_idx < self.system.mem.len()
        } implies self.system.mem.index(word_index_spec((pte.frame.base + ((vmem_idx * WORD_SIZE as nat) - base)) as nat)) === #[trigger] self.interp().mem.index(vmem_idx)
        by {
            let pt = self.interp_pt_mem();
            let sys_mem = self.system.mem;
            let vaddr = vmem_idx * WORD_SIZE as nat;
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            if self.system.mem.index(pmem_idx) !== self.interp().mem.index(vmem_idx) {
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

    proof fn lemma_interp_other(self, other: OSVariables)
        requires
            other.system.mem === self.system.mem,
            forall|base, pte| self.effective_mappings().contains_pair(base, pte) ==> other.effective_mappings().contains_pair(base, pte),
            self.inv(),
            other.inv(),
        ensures
            forall|word_idx: nat|
                self.interp().mem.dom().contains(word_idx)
                ==> {
                    &&& other.interp().mem.dom().contains(word_idx)
                    &&& #[trigger] other.interp().mem.index(word_idx) == #[trigger] self.interp().mem.index(word_idx)
                },
    {
        assert forall|word_idx: nat|
            self.interp().mem.dom().contains(word_idx)
            implies {
                &&& other.interp().mem.dom().contains(word_idx)
                &&& #[trigger] other.interp().mem.index(word_idx) == #[trigger] self.interp().mem.index(word_idx)
            } by
        {
            let vaddr = word_idx * WORD_SIZE as nat;
            let self_mappings = self.effective_mappings();
            let other_mappings = other.effective_mappings();
            let phys_mem_size = self.interp_constants().phys_mem_size;
            assert(hlspec::mem_domain_from_mappings_contains(phys_mem_size, word_idx, self_mappings));
            let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] self_mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            assert(self_mappings.contains_pair(base, pte));
            assert(between(vaddr, base, base + pte.frame.size));
            assert(other_mappings.contains_pair(base, pte));

            assert(other.interp().mem.dom().contains(word_idx));
            if other.interp().mem[word_idx] !== self.interp().mem[word_idx] {
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
}

pub open spec fn step_HW(s1: OSVariables, s2: OSVariables, system_step: hardware::HWStep) -> bool {
    &&& !system_step.is_PTMemOp()
    &&& hardware::next_step(s1.system, s2.system, system_step)
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
}

pub open spec fn step_Map(s1: OSVariables, s2: OSVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& hardware::step_PTMemOp(s1.system, s2.system)
    &&& spec_pt::step_Map(s1.pt_variables(), s2.pt_variables(), base, pte, result)
}

pub open spec fn step_Unmap(s1: OSVariables, s2: OSVariables, base: nat, result: UnmapResult) -> bool {
    let pte = s1.interp_pt_mem().index(base);
    // The system step tells us that s2.tlb is a submap of s1.tlb, so all we need to specify is
    // that s2.tlb doesn't contain this particular entry.
    &&& !s2.system.tlb.dom().contains(base)
    &&& hardware::step_PTMemOp(s1.system, s2.system)
    &&& spec_pt::step_Unmap(s1.pt_variables(), s2.pt_variables(), base, result)
}

pub enum OSStep {
    HW     { step: hardware::HWStep },
    Map    { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap  { vaddr: nat, result: UnmapResult },
}

impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { step } =>
                match step {
                    hardware::HWStep::IoOp { vaddr, paddr, op, pte }  => hlspec::AbstractStep::IoOp { vaddr, op, pte },
                    hardware::HWStep::PTMemOp                         => arbitrary(),
                    hardware::HWStep::TLBFill { vaddr, pte }          => hlspec::AbstractStep::Stutter,
                    hardware::HWStep::TLBEvict { vaddr }              => hlspec::AbstractStep::Stutter,
                },
            OSStep::Map    { vaddr, pte, result } => hlspec::AbstractStep::Map { vaddr, pte, result },
            OSStep::Unmap  { vaddr, result }      => hlspec::AbstractStep::Unmap { vaddr, result },
        }
    }
}

pub open spec fn next_step(s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW     { step }               => step_HW(s1, s2, step),
        OSStep::Map    { vaddr, pte, result } => step_Map(s1, s2, vaddr, pte, result),
        OSStep::Unmap  { vaddr, result }      => step_Unmap(s1, s2, vaddr, result),
    }
}

pub open spec fn next(s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(s1, s2, step)
}

pub open spec fn init(s: OSVariables) -> bool {
    hardware::init(s.system)
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
        s.inv();

proof fn next_step_preserves_inv(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step)
    ensures
        s2.inv(),
{
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
                s1.lemma_pt_mappings_dont_overlap_in_pmem(s2);
                assert(s2.pt_mappings_dont_overlap_in_pmem());
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
                assert(s2.pt_mappings_dont_overlap_in_vmem());
                assert forall|base2, pte2|
                    s2.system.tlb.contains_pair(base2, pte2)
                    implies #[trigger] s2.interp_pt_mem().contains_pair(base2, pte2) by
                {
                    assert(s1.system.tlb.contains_pair(base2, pte2));
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
                s1.lemma_pt_mappings_dont_overlap_in_pmem(s2);
                assert(s2.inv());
            } else {
                assert(s2.inv());
            }
        },
    }
}

// TODO: move the untrusted stuff of the refinement proof to separate file
proof fn next_step_refines_hl_next_step(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step)
    ensures
        hlspec::next_step(s1.interp_constants(), s1.interp(), s2.interp(), step.interp())
{
    next_step_preserves_inv(s1, s2, step);
    s1.lemma_effective_mappings_equal_interp_pt_mem();
    s2.lemma_effective_mappings_equal_interp_pt_mem();
    let abs_s1   = s1.interp();
    let abs_s2   = s2.interp();
    let abs_c    = s1.interp_constants();
    let sys_s1   = s1.system;
    let sys_s2   = s2.system;
    let pt1      = s1.interp_pt_mem();
    let pt2      = s2.interp_pt_mem();
    let abs_step = step.interp();
    match step {
        OSStep::HW { step: system_step } => {
            s1.lemma_effective_mappings_other(s2);
            match system_step {
                hardware::HWStep::IoOp { vaddr, paddr, op, pte } => {
                    // hlspec::AbstractStep::IoOp { vaddr, op, pte }
                    let pmem_idx = word_index_spec(paddr);
                    let vmem_idx = word_index_spec(vaddr);
                    assert(sys_s2.pt_mem === sys_s1.pt_mem);
                    assert(sys_s2.tlb === sys_s1.tlb);
                    match pte {
                        Some((base, pte)) => {
                            s1.lemma_interp();
                            s2.lemma_interp();

                            // system
                            assert(sys_s1.tlb.contains_pair(base, pte));
                            assert(between(vaddr, base, base + pte.frame.size));
                            assert(paddr === (pte.frame.base + (vaddr - base)) as nat);

                            // abs
                            assert(abs_s1.mappings.contains_pair(base, pte));
                            match op {
                                IoOp::Store { new_value, result } => {
                                    if pmem_idx < sys_s1.mem.len() && !pte.flags.is_supervisor && pte.flags.is_writable {
                                        assert(result.is_Ok());
                                        assert(sys_s2.mem === sys_s1.mem.update(pmem_idx, new_value));
                                        assert(hlspec::mem_domain_from_mappings_contains(abs_c.phys_mem_size, vmem_idx, s1.interp_pt_mem()));
                                        assert(abs_s1.mem.dom() === abs_s2.mem.dom());

                                        assert(sys_s1.mem.index(pmem_idx) == abs_s1.mem.index(vmem_idx));

                                        assert(abs_s1.mem.dom().contains(vmem_idx));
                                        assert(abs_s1.mem.insert(vmem_idx, new_value).dom() === abs_s1.mem.dom().insert(vmem_idx));
                                        assume(abs_s1.mem.dom() === abs_s1.mem.dom().insert(vmem_idx));
                                        // FIXME: ill-typed AIR
                                        // assert_sets_equal!(abs_s1.mem.dom(), abs_s1.mem.dom().insert(vmem_idx));
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
                                                assert(abs_s1.mem.index(vmem_idx2) == s1.system.mem.index(pmem_idx2));
                                                assert(abs_s2.mem.index(vmem_idx2) == s2.system.mem.index(pmem_idx2));
                                                assert(s2.system.mem === s1.system.mem.update(pmem_idx, new_value));
                                                assert(pmem_idx < s1.system.mem.len());
                                                assert(pmem_idx2 < s1.system.mem.len());
                                                // FIXME:
                                                assume(aligned(paddr, 8));
                                                assume(aligned(paddr2, 8));
                                                if pmem_idx == pmem_idx2 {
                                                    assert(vaddr != vaddr2);
                                                    assert(pte === pte2);
                                                    assert(vaddr - base != vaddr2 - base);
                                                    assert(paddr != paddr2);
                                                    assert(paddr  == (pte.frame.base + (vaddr - base)) as nat);
                                                    assert(paddr2 == (pte2.frame.base + (vaddr2 - base2)) as nat);
                                                    assert(false);
                                                }
                                                assert(s1.system.mem.index(pmem_idx2) == s2.system.mem.index(pmem_idx2));

                                                assert(abs_s2.mem.index(vmem_idx2) == abs_s1.mem.index(vmem_idx2));
                                            }
                                        };
                                        assert_maps_equal!(abs_s2.mem, abs_s1.mem.insert(vmem_idx, new_value));
                                        assert(hlspec::step_IoOp(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(sys_s2.mem === sys_s1.mem);
                                        assert(hlspec::step_IoOp(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    }
                                },
                                IoOp::Load { is_exec, result } => {
                                    assert(sys_s2.mem === sys_s1.mem);
                                    if pmem_idx < sys_s1.mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                                        assert(result.is_Value());
                                        assert(result.get_Value_0() == sys_s1.mem.index(pmem_idx));
                                        assert(hlspec::mem_domain_from_mappings_contains(abs_c.phys_mem_size, vmem_idx, s1.interp_pt_mem()));
                                        assert(sys_s1.mem.index(pmem_idx) == abs_s1.mem.index(vmem_idx));
                                        assert(hlspec::step_IoOp(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(hlspec::step_IoOp(abs_c, abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    }
                                },
                            }
                        },
                        None => {
                            assert(hlspec::step_IoOp(abs_c, abs_s1, abs_s2, vaddr, op, pte));
                        },
                    }
                    assert(hlspec::step_IoOp(abs_c, abs_s1, abs_s2, vaddr, op, pte));
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
            assert(hlspec::step_Map_preconditions(vaddr, pte));
            if candidate_mapping_overlaps_existing_vmem(pt_s1.map, vaddr, pte) {
                assert(candidate_mapping_overlaps_existing_vmem(abs_s1.mappings, vaddr, pte));
                assert(hlspec::step_Map(abs_c, abs_s1, abs_s2, vaddr, pte, result));
            } else {
                assert(!candidate_mapping_overlaps_existing_vmem(abs_s1.mappings, vaddr, pte));
                assert(forall|base, pte| s1.interp_pt_mem().contains_pair(base, pte) ==> s2.interp_pt_mem().contains_pair(base, pte));
                assert(forall|base, pte| s1.interp().mappings.contains_pair(base, pte) ==> s2.interp().mappings.contains_pair(base, pte));
                assert(s1.interp().mappings === s1.interp_pt_mem());
                assert(s2.interp().mappings === s2.interp_pt_mem());
                s1.lemma_interp_other(s2);
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
            assert(hlspec::step_Unmap_preconditions(vaddr));
            if pt_s1.map.dom().contains(vaddr) {
                assert(abs_s1.mappings.dom().contains(vaddr));
                assert(result.is_Ok());
                assert(pt_s2.map === pt_s1.map.remove(vaddr));
                assert(abs_s2.mappings === abs_s1.mappings.remove(vaddr));

                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(abs_c.phys_mem_size, abs_s2.mappings));
                s2.lemma_interp_other(s1);
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
    }
}

// // TODO: Can we add this to pervasive? Push is awkward to use in recursive functions.
// impl<A> Seq<A> {
//     pub open spec fn cons(self, a: A) -> Self;
// }

// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_cons_len<A>(s: Seq<A>, a: A)
//     ensures
//         #[trigger] s.cons(a).len() == s.len() + 1,
// {
// }

// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_cons_index_same<A>(s: Seq<A>, a: A)
//     ensures
//         #[trigger] s.cons(a).index(0) === a,
// {
// }

// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
//     requires
//         0 < i <= s.len(),
//     ensures
//         s.cons(a)[i] === s[i - 1],
// {
// }

// // exclusive on upper bound
// pub open spec fn enum_from_to(from: nat, to: nat) -> Seq<nat>
//     decreases to + 1 - from
// {
//     if from >= to {
//         seq![]
//     } else {
//         enum_from_to(from + 1, to).cons(from)
//     }
// }

// pub proof fn lemma_enum_from_to(from: nat, to: nat)
//     ensures
//         from <= to ==> enum_from_to(from, to).len() == to - from,
//         from > to ==> enum_from_to(from, to).len() == 0,
//         forall|i: nat|
//             i < enum_from_to(from, to).len() ==> enum_from_to(from, to)[i] == from + i
//     decreases to + 1 - from
// {
//     if from <= to {
//         lemma_enum_from_to(from + 1, to);
//     }
// }

// // TODO: better way of writing this? Maybe directly axiomatize like for Map?
// pub open spec fn new_seq_map_index<T, F: Fn(nat) -> T>(len: nat, f: F) -> Seq<T> {
//     enum_from_to(0, len).map(|idx,i| f(i))
// }

}
