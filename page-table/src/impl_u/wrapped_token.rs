use vstd::prelude::*;
use vstd::{ assert_by_contradiction, assert_seqs_equal };

use crate::spec_t::os;
use crate::spec_t::os_invariant;
use crate::spec_t::mmu::{ self, WalkResult };
use crate::spec_t::os_ext;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    aligned, bit, candidate_mapping_overlaps_existing_vmem, WORD_SIZE,
    bitmask_inc, x86_arch_spec, x86_arch_spec_upper_bound, MAX_BASE, align_to_usize
};
use crate::spec_t::mmu::defs::{
    MemRegionExec, MemRegion, PTE, MAX_PHYADDR, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE,
    L3_ENTRY_SIZE
};
use crate::spec_t::mmu::translation::{
    MASK_NEG_DIRTY_ACCESS, l0_bits, l1_bits, l2_bits, l3_bits,
    GPDE, PDE,
};
use crate::theorem::RLbl;
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::os_code_vc::Token;
#[cfg(verus_keep_ghost)]
use crate::spec_t::os_code_vc::{ lemma_concurrent_trs, unchanged_state_during_concurrent_trs, lemma_concurrent_trs_no_lock };
use crate::impl_u::wrapped_token;
use crate::impl_u::l2_impl::{ PT, PTDir };

verus! {

pub enum OpArgs {
    Map { base: usize, pte: PTE },
    Unmap { base: usize },
}

/// We define a view of the wrapped tokens with the memory stuff that the implementation uses to
/// define its invariant and interpretation. This way read-only ops (e.g. `read`) leave the view
/// fully unchanged, which simplifies reasoning. Otherwise we have to argue that the invariant is
/// preserved as only irrelevant parts of the state may have changed. (Since `read` still has to
/// take a mut ref as it changes the underlying token.)
pub struct WrappedTokenView {
    pub orig_st: os::State,
    pub args: OpArgs,
    pub change_made: bool,
    pub regions: Map<MemRegion, Seq<usize>>,
    /// We also keep the flat memory directly because this is what the MMU's interpretation is
    /// defined on.
    pub pt_mem: mmu::pt_mem::PTMem,
    // result is only relevant for mapping (TODO: and maybe we can get rid of it there?)
    pub result: Result<(),()>,
}

impl WrappedTokenView {
    pub open spec fn read(self, idx: usize, r: MemRegion) -> usize {
        self.regions[r][idx as int] & MASK_NEG_DIRTY_ACCESS
    }

    pub open spec fn interp(self) -> Map<usize, PTE> {
        self.pt_mem@
    }

    pub open spec fn write(self, idx: usize, value: usize, r: MemRegion, change: bool) -> WrappedTokenView {
        WrappedTokenView {
            regions: self.regions.insert(r, self.regions[r].update(idx as int, value)),
            pt_mem: self.pt_mem.write(add(r.base as usize, mul(idx, 8)), value),
            change_made: self.change_made || change,
            result: if change { Ok(()) } else { self.result },
            ..self
        }
    }

    pub open spec fn regions_derived_from_view(self) -> bool {
        forall|r| self.regions.contains_key(r) ==> #[trigger] self.regions[r] == Seq::new(512, |i: int| self.pt_mem.mem[(r.base + i * 8) as usize])
    }

    pub proof fn lemma_interps_match_aux1(self, pt: PTDir)
        requires
            PT::inv(self, pt),
            self.regions_derived_from_view(),
        ensures PT::interp(self, pt).interp().dom().subset_of(self.pt_mem@.dom().map(|k| k as nat))
    {
        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
        assert forall|vaddr: nat|
            PT::interp(self, pt).interp().contains_key(vaddr)
                implies {
            &&& vaddr <= usize::MAX
            &&& self.pt_mem.is_base_pt_walk(vaddr as usize)
        } by {
            x86_arch_spec_upper_bound();
            assert_by_contradiction!(vaddr < MAX_BASE, {
                assert_by_contradiction!(!PT::interp(self, pt).interp().contains_key(vaddr), {
                    broadcast use crate::impl_u::l2_impl::PT::lemma_inv_implies_interp_inv;
                    PT::interp(self, pt).lemma_interp_aux_between(0, vaddr, PT::interp(self, pt).interp()[vaddr]);
                });
            });
            assert(vaddr == vaddr as usize);
            let vaddr: usize = vaddr as usize;
            PT::lemma_interp_at_facts(self, pt, 0, self.pt_mem.pml4, 0);
            crate::spec_t::mmu::translation::lemma_bit_indices_less_512(vaddr as usize);
            assert(forall|x: usize, b: usize| x & b & b == x & b) by (bit_vector);

            let l0_bidx = l0_bits!(vaddr);
            let l1_bidx = l1_bits!(vaddr);
            let l2_bidx = l2_bits!(vaddr);
            let l3_bidx = l3_bits!(vaddr);

            let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
            let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
            let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
            let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
            assert(forall|a:usize| (a & bitmask_inc!(0usize,8usize) == a) ==> a < 512) by (bit_vector);
            assert(bitmask_inc!(39usize,47usize) == 0xFF80_0000_0000) by (compute);
            assert(bitmask_inc!(30usize,38usize) == 0x007F_C000_0000) by (compute);
            assert(bitmask_inc!(21usize,29usize) == 0x0000_3FE0_0000) by (compute);
            assert(bitmask_inc!(12usize,20usize) == 0x0000_001F_F000) by (compute);
            let interp_l0 = PT::interp(self, pt);
            let interp_l0_entry = PT::interp_at_entry(self, pt, 0, self.pt_mem.pml4, 0, l0_bidx as nat);
            crate::impl_u::l2_impl::PT::lemma_inv_implies_interp_inv(self, pt, 0, self.pt_mem.pml4, 0);
            interp_l0.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
            assert(interp_l0.index_for_vaddr(vaddr as nat) == x86_arch_spec.index_for_vaddr(0, 0, vaddr as nat));
            assert(interp_l0.interp_of_entry(interp_l0.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));
            let l0_addr = add(self.pt_mem.pml4, l0_idx);
            let l0e = PDE { entry: self.pt_mem.read(l0_addr), layer: Ghost(0) };
            let impl_l0e = PT::entry_at_spec(self, pt, 0, self.pt_mem.pml4, l0_bidx as nat);
            assert(self.pt_mem.read(l0_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l0_bidx as nat as usize, pt.region));
            assert(l0e@ == impl_l0e@) by {
                l0e.lemma_view_unchanged_dirty_access(impl_l0e);
            };

            let low_bits: usize = vaddr % (L0_ENTRY_SIZE as usize);
            // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + low_bits
            assert((l0_bidx << 39usize) | low_bits
                   == add(mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                          low_bits)) by (bit_vector)
                requires
                    low_bits == vaddr % mul(512, mul(512, mul(512, 4096)));
            assert(vaddr == ((l0_bidx << 39usize) | low_bits)) by (bit_vector)
                requires
                    l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                    vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                    low_bits == vaddr % mul(512, mul(512, mul(512, 4096)));

            match l0e@ {
                GPDE::Directory { addr: l1_daddr, .. } => {
                    assert(interp_l0_entry is Directory);
                    let l1_addr = add(l1_daddr, l1_idx);
                    let l1e = PDE { entry: self.pt_mem.read(l1_addr), layer: Ghost(1) };
                    let l1_base = x86_arch_spec.entry_base(0, 0, l0_bidx as nat);
                    let l1_ghost_pt = pt.entries[l0_bidx as int].get_Some_0();
                    assert(PT::directories_obey_invariant_at(self, pt, 0, self.pt_mem.pml4));
                    assert(PT::inv_at(self, l1_ghost_pt, 1, l1_daddr));
                    PT::lemma_interp_at_facts(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    let interp_l1 = PT::interp_at(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    let interp_l1_entry = PT::interp_at_entry(self, l1_ghost_pt, 1, l1_daddr, l1_base, l1_bidx as nat);
                    crate::impl_u::l2_impl::PT::lemma_inv_implies_interp_inv(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    interp_l1.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
                    assert(interp_l1.interp_of_entry(interp_l1.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));

                    let impl_l1e = PT::entry_at_spec(self, l1_ghost_pt, 1, l1_daddr, l1_bidx as nat);
                    assert(l1e@ == impl_l1e@) by {
                        assert(self.pt_mem.read(l1_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l1_bidx, l1_ghost_pt.region));
                        l1e.lemma_view_unchanged_dirty_access(impl_l1e);
                    };

                    let low_bits = vaddr % L1_ENTRY_SIZE;
                    // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + low_bits
                    assert((l0_bidx << 39usize) | (l1_bidx << 30usize) | low_bits
                           == add(add(mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                                      mul(l1_bidx, mul(512, mul(512, 4096)))),
                                      low_bits)) by (bit_vector)
                        requires
                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                            low_bits == vaddr % mul(512, mul(512, 4096));
                    assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | low_bits)) by (bit_vector)
                        requires
                            l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                            vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                            low_bits == vaddr % mul(512, mul(512, 4096));

                    match l1e@ {
                        GPDE::Page { addr: page_addr, .. } => {
                            let l2_base = x86_arch_spec.entry_base(1, l1_base, l1_bidx as nat);
                            assert(aligned(l2_base, L1_ENTRY_SIZE as nat)) by {
                                crate::impl_u::indexing::lemma_entry_base_from_index(l1_base, l1_bidx as nat, L1_ENTRY_SIZE as nat);
                            };
                            assert(interp_l1.interp_of_entry(l1_bidx as nat).dom() =~= set![l2_base as nat]);
                            assert(self.pt_mem.is_base_pt_walk(vaddr));
                        },
                        GPDE::Directory { addr: l2_daddr, .. } => {
                            assert(interp_l1_entry is Directory);
                            let l2_addr = add(l2_daddr, l2_idx);
                            let l2e = PDE { entry: self.pt_mem.read(l2_addr), layer: Ghost(2) };
                            let l2_base = x86_arch_spec.entry_base(1, l1_base, l1_bidx as nat);
                            let l2_ghost_pt = l1_ghost_pt.entries[l1_bidx as int].get_Some_0();
                            assert(PT::directories_obey_invariant_at(self, l1_ghost_pt, 1, l1_daddr));
                            assert(PT::inv_at(self, l2_ghost_pt, 2, l2_daddr));
                            PT::lemma_interp_at_facts(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            let interp_l2 = PT::interp_at(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            let interp_l2_entry = PT::interp_at_entry(self, l2_ghost_pt, 2, l2_daddr, l2_base, l2_bidx as nat);
                            crate::impl_u::l2_impl::PT::lemma_inv_implies_interp_inv(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            interp_l2.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
                            assert(interp_l2.interp_of_entry(interp_l2.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));

                            let impl_l2e = PT::entry_at_spec(self, l2_ghost_pt, 2, l2_daddr, l2_bidx as nat);
                            assert(l2e@ == impl_l2e@) by {
                                assert(self.pt_mem.read(l2_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l2_bidx, l2_ghost_pt.region));
                                l2e.lemma_view_unchanged_dirty_access(impl_l2e);
                            };

                            let low_bits: usize = vaddr % (L2_ENTRY_SIZE as usize);
                            // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + l2_bidx * L2_ENTRY_SIZE + low_bits
                            assert((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | low_bits
                                   == add(add(add(
                                          mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                                          mul(l1_bidx, mul(512, mul(512, 4096)))),
                                          mul(l2_bidx, mul(512, 4096))),
                                          low_bits)) by (bit_vector)
                                requires
                                    l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                    l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                    low_bits == vaddr % mul(512, 4096);
                            assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | low_bits)) by (bit_vector)
                                requires
                                    l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                    l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                    l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                    vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                    low_bits == vaddr % mul(512, 4096);

                            match l2e@ {
                                GPDE::Page { addr: page_addr, .. } => {
                                    let l3_base = x86_arch_spec.entry_base(2, l2_base, l2_bidx as nat);
                                    assert(aligned(l3_base, L2_ENTRY_SIZE as nat)) by {
                                        crate::impl_u::indexing::lemma_entry_base_from_index(0, l0_bidx as nat, L0_ENTRY_SIZE as nat);
                                        crate::impl_u::indexing::lemma_entry_base_from_index(l1_base, l1_bidx as nat, L1_ENTRY_SIZE as nat);
                                        crate::impl_u::indexing::lemma_entry_base_from_index(l2_base, l2_bidx as nat, L2_ENTRY_SIZE as nat);
                                    };
                                    assert(interp_l2.interp_of_entry(l2_bidx as nat).dom() =~= set![l3_base as nat]);
                                    assert(align_to_usize(vaddr, L2_ENTRY_SIZE) == vaddr);
                                    assert(self.pt_mem.is_base_pt_walk(vaddr));
                                },
                                GPDE::Directory { addr: l3_daddr, .. } => {
                                    assert(interp_l2_entry is Directory);
                                    let l3_addr = add(l3_daddr, l3_idx);
                                    let l3e = PDE { entry: self.pt_mem.read(l3_addr), layer: Ghost(3) };
                                    let l3_base = x86_arch_spec.entry_base(2, l2_base, l2_bidx as nat);
                                    let l3_ghost_pt = l2_ghost_pt.entries[l2_bidx as int].get_Some_0();
                                    assert(PT::directories_obey_invariant_at(self, l2_ghost_pt, 2, l2_daddr));
                                    assert(PT::inv_at(self, l3_ghost_pt, 3, l3_daddr));
                                    PT::lemma_interp_at_facts(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    let interp_l3 = PT::interp_at(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    let interp_l3_entry = PT::interp_at_entry(self, l3_ghost_pt, 3, l3_daddr, l3_base, l3_bidx as nat);
                                    crate::impl_u::l2_impl::PT::lemma_inv_implies_interp_inv(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    interp_l3.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
                                    assert(interp_l3.interp_of_entry(interp_l3.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));

                                    let impl_l3e = PT::entry_at_spec(self, l3_ghost_pt, 3, l3_daddr, l3_bidx as nat);
                                    assert(l3e@ == impl_l3e@) by {
                                        assert(self.pt_mem.read(l3_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l3_bidx, l3_ghost_pt.region));
                                        l3e.lemma_view_unchanged_dirty_access(impl_l3e);
                                    };

                                    let low_bits = vaddr % L3_ENTRY_SIZE;
                                    // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + l2_bidx * L2_ENTRY_SIZE + l3_bidx * L3_ENTRY_SIZE + low_bits
                                    assert((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | (l3_bidx << 12usize) | low_bits
                                           == add(add(add(add(
                                                  mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                                                  mul(l1_bidx, mul(512, mul(512, 4096)))),
                                                  mul(l2_bidx, mul(512, 4096))),
                                                  mul(l3_bidx, 4096)),
                                                  low_bits)) by (bit_vector)
                                        requires
                                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                            l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                            l3_bidx == (vaddr & 0x0000_001F_F000) >> 12,
                                            low_bits == vaddr % 4096;
                                    assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | (l3_bidx << 12usize) | low_bits)) by (bit_vector)
                                        requires
                                            l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                            l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                            l3_bidx == (vaddr & 0x0000_001F_F000) >> 12,
                                            vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                            low_bits == vaddr % 4096;

                                    match l3e@ {
                                        GPDE::Page { addr: page_addr, .. } => {
                                            let l4_base = x86_arch_spec.entry_base(3, l3_base, l3_bidx as nat);
                                            assert(aligned(l4_base, L3_ENTRY_SIZE as nat)) by {
                                                crate::impl_u::indexing::lemma_entry_base_from_index(0, l0_bidx as nat, L0_ENTRY_SIZE as nat);
                                                crate::impl_u::indexing::lemma_entry_base_from_index(l1_base, l1_bidx as nat, L1_ENTRY_SIZE as nat);
                                                crate::impl_u::indexing::lemma_entry_base_from_index(l2_base, l2_bidx as nat, L2_ENTRY_SIZE as nat);
                                                crate::impl_u::indexing::lemma_entry_base_from_index(l3_base, l3_bidx as nat, L3_ENTRY_SIZE as nat);
                                            };
                                            assert(interp_l3.interp_of_entry(l3_bidx as nat).dom() =~= set![l4_base as nat]);
                                            assert(align_to_usize(vaddr, L3_ENTRY_SIZE) == vaddr);
                                            assert(self.pt_mem.is_base_pt_walk(vaddr));
                                        },
                                        GPDE::Directory { .. } => assert(false),
                                        GPDE::Invalid => assert(false),
                                    }
                                },
                                GPDE::Invalid => assert(false),
                            }
                        },
                        GPDE::Invalid => assert(false),
                    }
                },
                GPDE::Page { .. } => assert(false),
                GPDE::Invalid => {
                    assert(!interp_l0.interp().contains_key(vaddr as nat));
                },
            };
        }
        assert forall|vaddr: nat|
            PT::interp(self, pt).interp().contains_key(vaddr)
                implies {
            &&& vaddr <= usize::MAX
            &&& self.pt_mem@.contains_key(vaddr as usize)
        } by {
            assert(forall|vaddr: usize| #![auto] self.pt_mem.is_base_pt_walk(vaddr) ==> self.pt_mem@.contains_key(vaddr));
        }
    }

    #[verifier(spinoff_prover)]
    pub proof fn lemma_interps_match_aux2(self, pt: PTDir)
        requires
            PT::inv(self, pt),
            self.regions_derived_from_view(),
        ensures
            forall|vaddr: nat|
                vaddr <= usize::MAX && #[trigger] self.pt_mem@.contains_key(vaddr as usize)
                    ==> PT::interp(self, pt).interp().contains_pair(vaddr, self.pt_mem@[vaddr as usize])
    {
        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
        assert forall|vaddr: nat|
            vaddr <= usize::MAX && #[trigger] self.pt_mem@.contains_key(vaddr as usize)
                implies
            PT::interp(self, pt).interp().contains_pair(vaddr, self.pt_mem@[vaddr as usize])
        by {
            assert(vaddr == vaddr as usize);
            let vaddr: usize = vaddr as usize;
            let pte = self.pt_mem@[vaddr as usize];
            assert(self.pt_mem.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte } && vbase == vaddr);
            PT::lemma_interp_at_facts(self, pt, 0, self.pt_mem.pml4, 0);
            crate::spec_t::mmu::translation::lemma_bit_indices_less_512(vaddr as usize);
            assert(forall|x: usize, b: usize| x & b & b == x & b) by (bit_vector);

            let l0_bidx = l0_bits!(vaddr);
            let l1_bidx = l1_bits!(vaddr);
            let l2_bidx = l2_bits!(vaddr);
            let l3_bidx = l3_bits!(vaddr);

            let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
            let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
            let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
            let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
            assert(forall|a:usize| (a & bitmask_inc!(0usize,8usize) == a) ==> a < 512) by (bit_vector);
            assert(bitmask_inc!(39usize,47usize) == 0xFF80_0000_0000) by (compute);
            assert(bitmask_inc!(30usize,38usize) == 0x007F_C000_0000) by (compute);
            assert(bitmask_inc!(21usize,29usize) == 0x0000_3FE0_0000) by (compute);
            assert(bitmask_inc!(12usize,20usize) == 0x0000_001F_F000) by (compute);
            let interp_l0 = PT::interp(self, pt);
            let interp_l0_entry = PT::interp_at_entry(self, pt, 0, self.pt_mem.pml4, 0, l0_bidx as nat);
            broadcast use crate::impl_u::l2_impl::PT::lemma_inv_implies_interp_inv;
            interp_l0.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l0_bidx as nat);
            let l0_addr = add(self.pt_mem.pml4, l0_idx);
            let l0e = PDE { entry: self.pt_mem.read(l0_addr), layer: Ghost(0) };
            let impl_l0e = PT::entry_at_spec(self, pt, 0, self.pt_mem.pml4, l0_bidx as nat);
            assert(self.pt_mem.read(l0_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l0_bidx as nat as usize, pt.region));
            assert(l0e@ == impl_l0e@) by {
                l0e.lemma_view_unchanged_dirty_access(impl_l0e);
            };
            match l0e@ {
                GPDE::Directory { addr: l1_daddr, .. } => {
                    assert(interp_l0_entry is Directory);
                    let l1_addr = add(l1_daddr, l1_idx);
                    let l1e = PDE { entry: self.pt_mem.read(l1_addr), layer: Ghost(1) };
                    let l1_base = x86_arch_spec.entry_base(0, 0, l0_bidx as nat);
                    let l1_ghost_pt = pt.entries[l0_bidx as int].get_Some_0();
                    assert(PT::directories_obey_invariant_at(self, pt, 0, self.pt_mem.pml4));
                    assert(PT::inv_at(self, l1_ghost_pt, 1, l1_daddr));
                    PT::lemma_interp_at_facts(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    let interp_l1 = PT::interp_at(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    let interp_l1_entry = PT::interp_at_entry(self, l1_ghost_pt, 1, l1_daddr, l1_base, l1_bidx as nat);
                    interp_l1.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l1_bidx as nat);

                    let impl_l1e = PT::entry_at_spec(self, l1_ghost_pt, 1, l1_daddr, l1_bidx as nat);
                    assert(l1e@ == impl_l1e@) by {
                        assert(self.pt_mem.read(l1_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l1_bidx, l1_ghost_pt.region));
                        l1e.lemma_view_unchanged_dirty_access(impl_l1e);
                    };
                    match l1e@ {
                        GPDE::Page { addr: page_addr, .. } => {
                            assert(aligned(vaddr as nat, L1_ENTRY_SIZE as nat));
                            assert(align_to_usize(vaddr, L1_ENTRY_SIZE) == vaddr) by (nonlinear_arith)
                                requires aligned(vaddr as nat, L1_ENTRY_SIZE as nat);
                            assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize))) by (bit_vector)
                                requires
                                    l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                    l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                    vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                    vaddr % mul(512, mul(512, 4096)) == 0;

                            assert(add(mul(l0_bidx, mul(512usize, mul(512, mul(512, 4096)))), mul(l1_bidx, mul(512usize, mul(512, 4096)))) == l0_bidx << 39usize | l1_bidx << 30usize) by (bit_vector)
                                requires l0_bidx < 512 && l1_bidx < 512;
                            // Previous assert proves: l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE == (l0_bidx as usize) << 39usize | (l1_bidx as usize) << 30usize

                            assert(interp_l1.interp_of_entry(l1_bidx as nat).contains_pair(vaddr as nat, pte)); // unstable
                            assert(interp_l1.interp().contains_pair(vaddr as nat, pte));
                            assert(interp_l0.interp().contains_pair(vaddr as nat, pte));
                        },
                        GPDE::Directory { addr: l2_daddr, .. } => {
                            assert(interp_l1_entry is Directory);
                            let l2_addr = add(l2_daddr, l2_idx);
                            let l2e = PDE { entry: self.pt_mem.read(l2_addr), layer: Ghost(2) };
                            let l2_base = x86_arch_spec.entry_base(1, l1_base, l1_bidx as nat);
                            let l2_ghost_pt = l1_ghost_pt.entries[l1_bidx as int].get_Some_0();
                            assert(PT::directories_obey_invariant_at(self, l1_ghost_pt, 1, l1_daddr));
                            assert(PT::inv_at(self, l2_ghost_pt, 2, l2_daddr));
                            PT::lemma_interp_at_facts(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            let interp_l2 = PT::interp_at(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            let interp_l2_entry = PT::interp_at_entry(self, l2_ghost_pt, 2, l2_daddr, l2_base, l2_bidx as nat);
                            interp_l2.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l2_bidx as nat);

                            let impl_l2e = PT::entry_at_spec(self, l2_ghost_pt, 2, l2_daddr, l2_bidx as nat);
                            assert(l2e@ == impl_l2e@) by {
                                assert(self.pt_mem.read(l2_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l2_bidx, l2_ghost_pt.region));
                                l2e.lemma_view_unchanged_dirty_access(impl_l2e);
                            };
                            match l2e@ {
                                GPDE::Page { addr: page_addr, .. } => {
                                    assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize))) by (bit_vector)
                                        requires
                                            l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                            l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                            vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                            vaddr % mul(512, 4096) == 0;

                                    assert(add(add(
                                            mul(l0_bidx, mul(512usize, mul(512, mul(512, 4096)))),
                                            mul(l1_bidx, mul(512usize, mul(512, 4096)))),
                                            mul(l2_bidx, mul(512, 4096)))
                                           == l0_bidx << 39usize | l1_bidx << 30usize | l2_bidx << 21usize) by (bit_vector)
                                        requires l0_bidx < 512 && l1_bidx < 512 && l2_bidx < 512;
                                    // Previous assert proves:
                                    // l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + l2_bidx * L2_ENTRY_SIZE
                                    // == (l0_bidx as usize) << 39usize | (l1_bidx as usize) << 30usize | (l2_bidx as usize) << 21usize

                                    assert(interp_l2.interp_of_entry(l2_bidx as nat).contains_pair(vaddr as nat, pte));
                                    assert(interp_l2.interp().contains_pair(vaddr as nat, pte));
                                    assert(interp_l1.interp().contains_pair(vaddr as nat, pte));
                                    assert(interp_l0.interp().contains_pair(vaddr as nat, pte));
                                },
                                GPDE::Directory { addr: l3_daddr, .. } => {
                                    assert(interp_l2_entry is Directory);
                                    let l3_addr = add(l3_daddr, l3_idx);
                                    let l3e = PDE { entry: self.pt_mem.read(l3_addr), layer: Ghost(3) };
                                    let l3_base = x86_arch_spec.entry_base(2, l2_base, l2_bidx as nat);
                                    let l3_ghost_pt = l2_ghost_pt.entries[l2_bidx as int].get_Some_0();
                                    assert(PT::directories_obey_invariant_at(self, l2_ghost_pt, 2, l2_daddr));
                                    assert(PT::inv_at(self, l3_ghost_pt, 3, l3_daddr));
                                    PT::lemma_interp_at_facts(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    let interp_l3 = PT::interp_at(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    let interp_l3_entry = PT::interp_at_entry(self, l3_ghost_pt, 3, l3_daddr, l3_base, l3_bidx as nat);
                                    interp_l3.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l3_bidx as nat);

                                    let impl_l3e = PT::entry_at_spec(self, l3_ghost_pt, 3, l3_daddr, l3_bidx as nat);
                                    assert(l3e@ == impl_l3e@) by {
                                        assert(self.pt_mem.read(l3_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l3_bidx, l3_ghost_pt.region));
                                        l3e.lemma_view_unchanged_dirty_access(impl_l3e);
                                    };
                                    match l3e@ {
                                        GPDE::Page { addr: page_addr, .. } => {
                                            assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | (l3_bidx << 12usize))) by (bit_vector)
                                                requires
                                                    l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                                    l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                                    l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                                    l3_bidx == (vaddr & 0x0000_001F_F000) >> 12,
                                                    vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                                    vaddr % 4096 == 0;

                                            assert(add(add(add(
                                                    mul(l0_bidx, mul(512usize, mul(512, mul(512, 4096)))),
                                                    mul(l1_bidx, mul(512usize, mul(512, 4096)))),
                                                    mul(l2_bidx, mul(512, 4096))),
                                                    mul(l3_bidx, 4096))
                                                   == l0_bidx << 39usize | l1_bidx << 30usize | l2_bidx << 21usize | l3_bidx << 12usize) by (bit_vector)
                                                requires l0_bidx < 512 && l1_bidx < 512 && l2_bidx < 512 && l3_bidx < 512;
                                            // Previous assert proves:
                                            // l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + l2_bidx * L2_ENTRY_SIZE + l3_bidx * L3_ENTRY_SIZE
                                            // == (l0_bidx as usize) << 39usize | (l1_bidx as usize) << 30usize | (l2_bidx as usize) << 21usize | (l3_bidx as usize) << 12usize

                                            assert(interp_l3.interp_of_entry(l3_bidx as nat).contains_pair(vaddr as nat, pte));
                                            assert(interp_l3.interp().contains_pair(vaddr as nat, pte));
                                            assert(interp_l2.interp().contains_pair(vaddr as nat, pte));
                                            assert(interp_l1.interp().contains_pair(vaddr as nat, pte));
                                            assert(interp_l0.interp().contains_pair(vaddr as nat, pte));
                                        },
                                        GPDE::Directory { .. } => assert(false),
                                        GPDE::Invalid => assert(false),
                                    }
                                },
                                GPDE::Invalid => assert(false),
                            }
                        },
                        GPDE::Invalid => assert(false),
                    }
                },
                _ => assert(false),
            };
        }
    }

    #[verifier(spinoff_prover)]
    pub proof fn lemma_interps_match(self, pt: PTDir)
        requires
            PT::inv(self, pt),
            self.regions_derived_from_view(),
        ensures PT::interp(self, pt).interp() == crate::spec_t::mmu::defs::nat_keys(self.interp())
    {
        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);

        self.lemma_interps_match_aux1(pt);
        self.lemma_interps_match_aux2(pt);

        assert(PT::interp_at(self, pt, 0, self.pt_mem.pml4, 0).interp() ==
            Map::new(|vaddr: nat| vaddr <= usize::MAX && self.pt_mem@.contains_key(vaddr as usize), |vaddr: nat| self.pt_mem@[vaddr as usize]));

        assert(PT::interp(self, pt).interp() =~= crate::spec_t::mmu::defs::nat_keys(self.interp()));
    }
}

pub tracked struct WrappedMapToken {
    tracked tok: Token,
    ghost change_made: bool,
    ghost orig_st: os::State,
}

impl WrappedMapToken {
    pub closed spec fn view(&self) -> WrappedTokenView {
        WrappedTokenView {
            orig_st: self.orig_st,
            args:
                OpArgs::Map {
                    base: self.orig_st.core_states[self.tok.core()]->MapExecuting_vaddr as usize,
                    pte: self.orig_st.core_states[self.tok.core()]->MapExecuting_pte,
                },
            change_made: self.change_made,
            regions:
                Map::new(
                    |r: MemRegion| self.tok.st().os_ext.allocated.contains(r),
                    |r: MemRegion| Seq::new(512, |i: int| self.tok.st().mmu@.pt_mem.mem[(r.base + i * 8) as usize])),
            pt_mem: self.tok.st().mmu@.pt_mem,
            result: self.tok.st().core_states[self.tok.core()]->MapDone_result,
        }
    }

    pub proof fn new(tracked tok: Token) -> (tracked res: WrappedMapToken)
        requires
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is MapExecuting,
            tok.thread() == tok.st().core_states[tok.core()]->MapExecuting_ult_id,
            tok.st().core_states[tok.core()]->MapExecuting_vaddr <= usize::MAX,
            tok.steps().len() == 1,
            tok.steps()[0] is MapEnd,
            tok.steps()[0]->MapEnd_vaddr == tok.st().core_states[tok.core()]->MapExecuting_vaddr,
            tok.steps()[0]->MapEnd_thread_id == tok.thread(),
            !tok.on_first_step(),
            tok.progress() is Ready,
            tok.st().inv(tok.consts()),
        ensures
            res.inv(),
            res@.orig_st == tok.st(),
            res@.pt_mem == tok.st().mmu@.pt_mem,
            res@.regions.dom() == tok.st().os_ext.allocated,
            tok.st().core_states[tok.core()] matches os::CoreState::MapExecuting { vaddr, pte, .. }
                && res@.args == (OpArgs::Map { base: vaddr as usize, pte }),
            !res@.change_made,
    {
        let tracked t = WrappedMapToken {
            tok,
            change_made: false,
            orig_st: tok.st(),
        };
        assert(t@.regions.dom() =~= tok.st().os_ext.allocated);
        assert(Map::new(
                |k| t.tok.st().mmu@.pt_mem@.contains_key(k) && !t@.orig_st.mmu@.pt_mem@.contains_key(k),
                |k| t.tok.st().mmu@.pt_mem@[k])
            =~= map![]);
        t
    }

    pub closed spec fn inv(&self) -> bool {
        // OSSM invariant
        &&& self.tok.st().inv(self.tok.consts())
        // Other stuff
        &&& !self.tok.on_first_step()
        &&& self.tok.consts().valid_core(self.tok.core())
        &&& self.tok.consts().valid_ult(self.tok.thread())
        &&& self.tok.progress() is Ready
        &&& self.tok.steps().len() == 1
        &&& self.tok.steps()[0] is MapEnd
        &&& self.tok.steps()[0]->MapEnd_thread_id == self.tok.thread()
        &&& if self.change_made {
            &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::MapDone { vaddr, pte, ult_id, result }
            &&& self.tok.steps()[0]->MapEnd_vaddr == vaddr
            &&& vaddr <= usize::MAX
            &&& self.tok.thread() == ult_id
            &&& self@.args == OpArgs::Map { base: vaddr as usize, pte }
        } else {
            &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::MapExecuting { vaddr, pte, ult_id }
            &&& self.tok.steps()[0]->MapEnd_vaddr == vaddr
            &&& self.tok.thread() == ult_id
            &&& vaddr <= usize::MAX
            &&& self@.args == OpArgs::Map { base: vaddr as usize, pte }
        }
    }

    pub proof fn lemma_regions_derived_from_view(self)
        requires self.inv()
        ensures self@.regions_derived_from_view()
    {}

    //spec fn regions_disjoint(self) -> bool {
    //    forall|i: nat, j: nat|
    //        i != j && i < pt.entries.len() && j < pt.entries.len()
    //        && #[trigger] pt.entries[j as int] is Some && #[trigger] pt.entries[i as int] is Some
    //        ==> pt.entries[i as int]->Some_0.used_regions.disjoint(pt.entries[j as int]->Some_0.used_regions)
    //}

    pub exec fn read(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, r: Ghost<MemRegion>) -> (res: usize)
        requires
            old(tok)@.regions.contains_key(r@),
            r@.base == pbase,
            idx < 512,
            old(tok).inv(),
        ensures
            res == tok@.read(idx, r@),
            tok@ == old(tok)@,
            tok.inv(),
    {
        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        assert(core == tok.tok.consts().ult2core[tok.tok.thread()]);
        assert(tok.tok.consts().valid_core(core));
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            mmu_tok.prophesy_read(addr);
            let post = os::State {
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };
            let read_result = mmu_tok.lbl()->Read_2;
            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(os::step_ReadPTMem(tok.tok.consts(), tok.tok.st(), post, core, addr, read_result, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::ReadPTMem { core, paddr: addr, value: read_result }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        let res = mmu::rl3::code::read(Tracked(&mut mmu_tok), addr);
        let ghost state2 = tok.tok.st();

        proof {
            broadcast use to_rl1::next_refines;
            assert(state1.mmu@.is_tso_read_deterministic(core, addr));
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let ghost state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
        }
        res & MASK_NEG_DIRTY_ACCESS
    }

    pub exec fn write_stutter(
        Tracked(tok): Tracked<&mut Self>,
        pbase: usize,
        idx: usize,
        value: usize,
        Ghost(r): Ghost<MemRegion>,
        Ghost(root_pt1): Ghost<PTDir>,
        Ghost(root_pt2): Ghost<PTDir>,
    )
        requires
            !old(tok)@.change_made,
            old(tok)@.regions.contains_key(r),
            r.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 1,
            old(tok)@.read(idx, r) & 1 == 0,
            PT::inv(old(tok)@, root_pt1),
            PT::inv(old(tok)@.write(idx, value, r, false), root_pt2),
            PT::interp_to_l0(old(tok)@.write(idx, value, r, false), root_pt2) == PT::interp_to_l0(old(tok)@, root_pt1),
        ensures
            tok@ == old(tok)@.write(idx, value, r, false),
            tok.inv(),
    {
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);

        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            old(tok)@.lemma_interps_match(root_pt1);
            old(tok).lemma_regions_derived_from_view_after_write(r, idx, value, false);
            old(tok)@.write(idx, value, r, false).lemma_interps_match(root_pt2);
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            let post = os::State { mmu: mmu_tok.post(), ..tok.tok.st() };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().common, mmu::rl1::Step::WriteNonneg, mmu_tok.lbl()));
            assert(os::step_MapOpStutter(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapOpStutter { core, paddr: addr, value }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
        let ghost state2 = tok.tok.st();

        proof {
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(unchanged_state_during_concurrent_trs(state2, state3, core));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            assert(tok.inv());
            assert(tok.tok.st().core_states[core] == old(tok).tok.st().core_states[core]);
            assert(tok@.regions[r] =~= old(tok)@.regions[r].update(idx as int, value));
            assert(tok@.regions[r] == tok@.regions[r].update(idx as int, value));
            assert(tok@.regions =~= old(tok)@.regions.insert(r, tok@.regions[r].update(idx as int, value)));
        }
    }

    pub exec fn write_change(
        Tracked(tok): Tracked<&mut Self>,
        pbase: usize,
        idx: usize,
        value: usize,
        Ghost(r): Ghost<MemRegion>,
        Ghost(root_pt): Ghost<PTDir>
    )
        requires
            !old(tok)@.change_made,
            old(tok)@.regions.contains_key(r),
            r.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 1,
            old(tok)@.read(idx, r) & 1 == 0,
            !candidate_mapping_overlaps_existing_vmem(
                PT::interp_to_l0(old(tok)@, root_pt),
                old(tok)@.args->Map_base as nat,
                old(tok)@.args->Map_pte
            ),
            PT::inv(old(tok)@, root_pt),
            PT::inv(old(tok)@.write(idx, value, r, true), root_pt),
            PT::interp_to_l0(old(tok)@.write(idx, value, r, true), root_pt)
                == PT::interp_to_l0(old(tok)@, root_pt).insert(old(tok)@.args->Map_base as nat, old(tok)@.args->Map_pte),
            //old(tok)@.write(idx, value, r).interp() == old(tok)@.interp().insert(old(tok)@.args->Map_base, old(tok)@.args->Map_pte),
        ensures
            tok@ == old(tok)@.write(idx, value, r, true),
            tok.inv(),
    {
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);

        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        let ghost vaddr = tok@.args->Map_base;
        let ghost pte = tok@.args->Map_pte;
        proof {
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            assert(tok.tok.st().core_states[core] is MapExecuting);
            assert(tok.tok.st().core_states[core] matches os::CoreState::MapExecuting { vaddr: v, pte: p, .. } && vaddr == v && pte == p);
            let new_cs = os::CoreState::MapDone { ult_id: tok.tok.thread(), vaddr: vaddr as nat, pte, result: Ok(()) };
            let post = os::State {
                core_states: tok.tok.st().core_states.insert(core, new_cs),
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().common, mmu::rl1::Step::WriteNonneg, mmu_tok.lbl()));
            old(tok)@.lemma_interps_match(root_pt);
            old(tok).lemma_regions_derived_from_view_after_write(r, idx, value, true);
            old(tok)@.write(idx, value, r, true).lemma_interps_match(root_pt);
            assert(os::step_MapOpChange(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapOpChange { core, paddr: addr, value }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
        let ghost state2 = tok.tok.st();
        proof { tok.change_made = true; }

        proof {
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(unchanged_state_during_concurrent_trs(state2, state3, core));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            assert(tok.inv());
        }
        assert(tok@.regions[r] =~= old(tok)@.regions[r].update(idx as int, value));
        assert(tok@.pt_mem == old(tok)@.pt_mem.write(add(r.base as usize, mul(idx, 8)), value));
        assert(tok@.regions =~= old(tok)@.regions.insert(r, old(tok)@.regions[r].update(idx as int, value)));
        assert(tok@ =~= old(tok)@.write(idx, value, r, true));
    }

    pub exec fn allocate(Tracked(tok): Tracked<&mut Self>, layer: usize) -> (res: MemRegionExec)
        requires
            !old(tok)@.change_made,
            old(tok).inv(),
        ensures
            aligned(res.base as nat, 4096),
            res.size == 4096,
            res.base + 4096 <= MAX_PHYADDR,
            !old(tok)@.regions.contains_key(res@),
            tok@.regions === old(tok)@.regions.insert(res@, seq![0; 512]),
            tok@.pt_mem == old(tok)@.pt_mem,
            tok@.args == old(tok)@.args,
            tok@.orig_st == old(tok)@.orig_st,
            tok@.result == old(tok)@.result,
            !tok@.change_made,
            tok.inv(),
    {
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut osext_tok = tok.tok.get_osext_token();
        proof {
            osext_tok.prophesy_allocate();
            let post = os::State { os_ext: osext_tok.post(), ..tok.tok.st() };
            assert(os::step_Allocate(tok.tok.consts(), tok.tok.st(), post, core, osext_tok.lbl()->Allocate_res, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::Allocate { core, res: osext_tok.lbl()->Allocate_res }, RLbl::Tau));
            tok.tok.register_internal_step_osext(&mut osext_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        let res = os_ext::code::allocate(Tracked(&mut osext_tok), layer);
        let ghost state2 = tok.tok.st();

        proof {
            tok.tok.return_osext_token(osext_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let ghost state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
        }
        assert(!old(tok)@.regions.contains_key(res@));
        proof {
            assert_seqs_equal!(tok@.regions[res@] == seq![0; 512], i => {
                let pa = (res@.base + i * 8) as usize;
                assert(aligned(pa as nat, 8));
                assert(tok.tok.consts().common.in_ptmem_range(pa as nat, 8));
                // From unallocated_memory_zeroed
                assert(tok@.pt_mem.read(pa) == 0);
            });
        }
        assert(tok@.regions =~= old(tok)@.regions.insert(res@, seq![0; 512]));
        res
    }

    /// If there's an overlapping mapping we don't write anything but just do a MapNoOp step.
    pub proof fn register_failed_map(tracked tok: &mut Self, root_pt: PTDir)
        requires
            !old(tok)@.change_made,
            old(tok).inv(),
            candidate_mapping_overlaps_existing_vmem(
                PT::interp_to_l0(old(tok)@, root_pt),
                old(tok)@.args->Map_base as nat,
                old(tok)@.args->Map_pte
            ),
            PT::inv(old(tok)@, root_pt),
        ensures
            tok@ == (WrappedTokenView { change_made: true, result: Err(()), ..old(tok)@ }),
            tok.inv(),
    {
        tok@.lemma_interps_match(root_pt);
        tok.change_made = true; // We didn't actually make a change but for mapping, this just
                                // indicates whether or not we're "done".

        let ghost core = tok.tok.core();
        let ghost vaddr = tok@.args->Map_base;
        let ghost pte = tok@.args->Map_pte;
        let new_cs = os::CoreState::MapDone { ult_id: tok.tok.thread(), vaddr: vaddr as nat, pte, result: Err(()) };
        let post = os::State {
            core_states: tok.tok.st().core_states.insert(core, new_cs),
            ..tok.tok.st()
        };

        assert(os::step_MapNoOp(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
        assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapNoOp { core }, RLbl::Tau));
        tok.tok.register_internal_step(post);
        os_invariant::next_preserves_inv(tok.tok.consts(), old(tok).tok.st(), tok.tok.st(), RLbl::Tau);
        let ghost state2 = tok.tok.st();
        let pidx = tok.tok.do_concurrent_trs();
        lemma_concurrent_trs(state2, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
    }

    pub exec fn finish_map_and_release_lock(Tracked(tok): Tracked<WrappedMapToken>) -> (rtok: Tracked<Token>)
        requires
            tok@.change_made,
            tok.inv(),
            forall|wtok: WrappedTokenView| ({
                &&& wtok.pt_mem == tok@.pt_mem
                &&& wtok.regions.dom() == tok@.regions.dom()
                &&& #[trigger] wtok.regions_derived_from_view()
            }) ==> exists|pt| PT::inv_and_nonempty(wtok, pt),
        ensures
            rtok@.progress() is Unready,
            rtok@.steps() === seq![],
            rtok@.steps_taken().last()->MapEnd_result == tok@.result,
    {
        let ghost core = tok.tok.core();
        let tracked mut tok = tok;
        let ghost state1 = tok.tok.st();
        let ghost vaddr = tok.tok.st().core_states[core]->MapDone_vaddr;
        let ghost result = tok.tok.st().core_states[core]->MapDone_result;

        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            mmu_tok.prophesy_barrier();
            let post = os::State {
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };
            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(os::step_Barrier(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::Barrier { core }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        let res = mmu::rl3::code::barrier(Tracked(&mut mmu_tok));
        let ghost state2 = tok.tok.st();

        proof {
            broadcast use to_rl1::next_refines;
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            lemma_concurrent_trs(state2, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
        }
        let ghost state3 = tok.tok.st();

        let tracked mut osext_tok = tok.tok.get_osext_token();

        proof {
            broadcast use to_rl1::next_refines;
            osext_tok.prophesy_release_lock();
            let post = os::State {
                core_states: tok.tok.st().core_states.insert(core, os::CoreState::Idle),
                os_ext: osext_tok.post(),
                ..tok.tok.st()
            };
            assert(os_ext::step_ReleaseLock(tok.tok.st().os_ext, post.os_ext, tok.tok.consts().common, osext_tok.lbl()));
            let lbl = RLbl::MapEnd { thread_id: tok.tok.thread(), vaddr, result };
            assert(post.inv_impl()) by {
                assert(tok.tok.st().mmu@.pt_mem == tok@.pt_mem);
                assert(tok.tok.st().os_ext.allocated == tok@.regions.dom());
            };
            assert(tok.tok.st().mmu@.pending_maps =~= map![]);
            assert(tok.tok.st().mmu@.writes.tso =~= set![]);
            assert(os::step_MapEnd(tok.tok.consts(), tok.tok.st(), post, core, lbl));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapEnd { core }, lbl));
            tok.tok.register_external_step_osext(&mut osext_tok, post, lbl);
            os_invariant::next_preserves_inv(tok.tok.consts(), state3, tok.tok.st(), lbl);
        }

        os_ext::code::release_lock(Tracked(&mut osext_tok));

        proof {
            broadcast use to_rl1::next_refines;
            tok.tok.return_osext_token(osext_tok);
            assert(tok.tok.steps() === seq![]);
        }
        Tracked(tok.tok)
    }

    pub proof fn lemma_regions_derived_from_view_after_write(self, r: MemRegion, idx: usize, value: usize, change: bool)
        requires
            self.inv(),
            self@.regions.contains_key(r),
            idx < 512,
        ensures
            self@.write(idx, value, r, change).regions_derived_from_view()
    {
        let self_write = self@.write(idx, value, r, change);
        assert forall|r2| self_write.regions.contains_key(r2)
            implies
            #[trigger] self_write.regions[r2] =~= Seq::new(512, |i: int| self_write.pt_mem.mem[(r2.base + i * 8) as usize])
        by {
        };
    }

}

pub exec fn start_map_and_acquire_lock(Tracked(tok): Tracked<&mut Token>, Ghost(vaddr): Ghost<nat>, Ghost(pte): Ghost<PTE>)
    requires
        os::step_Map_enabled(old(tok).consts(), vaddr, pte),
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).consts().valid_core(old(tok).core()), // TODO: ??
        old(tok).st().core_states[old(tok).core()] is Idle,
        old(tok).steps_taken() === seq![],
        old(tok).steps().len() == 2,
        old(tok).steps().first() == (RLbl::MapStart { thread_id: old(tok).thread(), vaddr, pte }),
        old(tok).progress() is Unready,
        old(tok).st().inv(old(tok).consts()),
    ensures
        tok.core() == old(tok).core(),
        tok.thread() == old(tok).thread(),
        tok.st().core_states[tok.core()] == (os::CoreState::MapExecuting { ult_id: tok.thread(), vaddr, pte }),
        tok.progress() is Ready,
        tok.st().os_ext.lock == Some(tok.core()),
        tok.st().inv(tok.consts()),
        tok.st().mmu@.pt_mem.pml4 == old(tok).st().mmu@.pt_mem.pml4,
        tok.consts() == old(tok).consts(),
        tok.steps() == old(tok).steps().drop_first(),
        tok.steps_taken() == seq![old(tok).steps().first()],
        !tok.on_first_step(),
        // From `inv_impl`:
        forall|wtok: wrapped_token::WrappedTokenView| ({
            &&& wtok.pt_mem == tok.st().mmu@.pt_mem
            &&& wtok.regions.dom() == tok.st().os_ext.allocated
            &&& #[trigger] wtok.regions_derived_from_view()
        }) ==> exists|pt| PT::inv_and_nonempty(wtok, pt),
{
    let ghost state1 = tok.st();
    let ghost core = tok.core();
    let ghost pidx = tok.do_concurrent_trs();
    let ghost state2 = tok.st();
    proof {
        lemma_concurrent_trs_no_lock(state1, state2, tok.consts(), core, pidx);
        let new_cs = os::CoreState::MapWaiting { ult_id: tok.thread(), vaddr, pte };
        let new_sound = tok.st().sound && os::step_Map_sound(tok.st().interp_pt_mem(), tok.st().core_states.values(), vaddr, pte);
        let post = os::State {
            core_states: tok.st().core_states.insert(core, new_cs),
            sound: new_sound,
            ..tok.st()
        };
        let lbl = RLbl::MapStart { thread_id: tok.thread(), vaddr, pte };
        assert(os::step_MapStart(tok.consts(), tok.st(), post, core, lbl));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapStart { core }, lbl));
        tok.register_external_step(post, lbl);
        let state3 = tok.st();
        os_invariant::next_preserves_inv(tok.consts(), state2, state3, lbl);
        let ghost pidx = tok.do_concurrent_trs();
        let state4 = tok.st();
        lemma_concurrent_trs_no_lock(state3, state4, tok.consts(), core, pidx);
    }


    let ghost state5 = tok.st();
    assert(core == tok.consts().ult2core[tok.thread()]);
    let tracked mut osext_tok = tok.get_osext_token();
    proof {
        osext_tok.prophesy_acquire_lock();
        let vaddr = tok.st().core_states[core]->MapWaiting_vaddr;
        let pte = tok.st().core_states[core]->MapWaiting_pte;
        let new_cs = os::CoreState::MapExecuting { ult_id: tok.thread(), vaddr, pte };
        let post = os::State {
            core_states: tok.st().core_states.insert(core, new_cs),
            os_ext: osext_tok.post(),
            ..tok.st()
        };
        //assert(os_ext::step_AcquireLock(tok.st().os_ext, post.os_ext, tok.consts().common, osext_tok.lbl()));
        assert(os::step_MapOpStart(tok.consts(), tok.st(), post, core, RLbl::Tau));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapOpStart { core }, RLbl::Tau));
        tok.register_internal_step_osext(&mut osext_tok, post);
        os_invariant::next_preserves_inv(tok.consts(), state5, tok.st(), RLbl::Tau);
    }

    os_ext::code::acquire_lock(Tracked(&mut osext_tok));
    let ghost state6 = tok.st();

    proof {
        tok.return_osext_token(osext_tok);
        let pidx = tok.do_concurrent_trs();
        let state7 = tok.st();
        lemma_concurrent_trs(state6, state7, tok.consts(), tok.core(), pidx);
        assert(tok.steps_taken() =~= seq![old(tok).steps().first()]);
    }
}



pub tracked struct WrappedUnmapToken {
    tracked tok: Token,
    ghost change_made: bool,
    ghost orig_st: os::State,
}

impl WrappedUnmapToken {
    pub closed spec fn view(&self) -> WrappedTokenView {
        WrappedTokenView {
            orig_st: self.orig_st,
            args:
                OpArgs::Unmap {
                    base: self.orig_st.core_states[self.tok.core()]->UnmapExecuting_vaddr as usize,
                },
            change_made: self.change_made,
            regions:
                Map::new(
                    |r: MemRegion| self.tok.st().os_ext.allocated.contains(r),
                    |r: MemRegion| Seq::new(512, |i: int| self.tok.st().mmu@.pt_mem.mem[(r.base + i * 8) as usize])),
            pt_mem: self.tok.st().mmu@.pt_mem,
            result: if self.tok.st().core_states[self.tok.core()]->UnmapExecuting_result->Some_0 is Ok { Ok(()) } else { Err(()) },
        }
    }

    pub proof fn new(tracked tok: Token) -> (tracked res: WrappedUnmapToken)
        requires
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is UnmapExecuting,
            tok.thread() == tok.st().core_states[tok.core()]->UnmapExecuting_ult_id,
            tok.st().core_states[tok.core()]->UnmapExecuting_result is None,
            tok.st().core_states[tok.core()]->UnmapExecuting_vaddr <= usize::MAX,
            tok.steps().len() == 1,
            tok.steps_taken().len() == 1,
            tok.steps()[0] is UnmapEnd,
            tok.steps()[0]->UnmapEnd_vaddr == tok.st().core_states[tok.core()]->UnmapExecuting_vaddr,
            tok.steps()[0]->UnmapEnd_thread_id == tok.thread(),
            !tok.on_first_step(),
            tok.progress() is Ready,
            tok.st().inv(tok.consts()),
        ensures
            res.inv(),
            res@.orig_st == tok.st(),
            res@.pt_mem == tok.st().mmu@.pt_mem,
            res@.regions.dom() == tok.st().os_ext.allocated,
            tok.st().core_states[tok.core()] matches os::CoreState::UnmapExecuting { vaddr, .. }
                && res@.args == (OpArgs::Unmap { base: vaddr as usize }),
            !res@.change_made,
    {
        let tracked t = WrappedUnmapToken {
            tok,
            change_made: false,
            orig_st: tok.st(),
        };
        assert(t@.regions.dom() =~= tok.st().os_ext.allocated);
        assert(Map::new(
                |k| t.tok.st().mmu@.pt_mem@.contains_key(k) && !t@.orig_st.mmu@.pt_mem@.contains_key(k),
                |k| t.tok.st().mmu@.pt_mem@[k])
            =~= map![]);
        t
    }

    pub closed spec fn inv(&self) -> bool {
        // OSSM invariant
        &&& self.tok.st().inv(self.tok.consts())
        // Other stuff
        &&& !self.tok.on_first_step()
        &&& self.tok.consts().valid_core(self.tok.core())
        &&& self.tok.consts().valid_ult(self.tok.thread())
        &&& self.tok.progress() is Ready
        &&& self.tok.steps().len() == 1
        &&& self.tok.steps_taken().len() == 1
        &&& self.tok.steps()[0] is UnmapEnd
        &&& self.tok.steps()[0]->UnmapEnd_thread_id == self.tok.thread()
        &&& self.tok.steps()[0]->UnmapEnd_vaddr <= usize::MAX
        &&& self.orig_st.core_states[self.tok.core()]->UnmapExecuting_vaddr == self.tok.steps()[0]->UnmapEnd_vaddr
        &&& if self.change_made {
            &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::UnmapExecuting { vaddr, ult_id, result: Some(Ok(pte)) }
            &&& vaddr == self.tok.steps()[0]->UnmapEnd_vaddr
            &&& ult_id == self.tok.thread()
            &&& pte == self.orig_st.interp_pt_mem()[vaddr]
            //&&& self@.args == OpArgs::Unmap { base: vaddr as usize }
        } else {
            &&& self.tok.st().mmu@.pt_mem == self.orig_st.mmu@.pt_mem
            &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::UnmapExecuting { vaddr, ult_id, result: None }
            &&& vaddr == self.tok.steps()[0]->UnmapEnd_vaddr
            &&& ult_id == self.tok.thread()
            //&&& self@.args == OpArgs::Unmap { base: vaddr as usize }
        }
    }

    pub proof fn lemma_regions_derived_from_view(self)
        requires self.inv()
        ensures self@.regions_derived_from_view()
    {}

    // TODO: This is 1:1 the same as read on WrappedMapToken. Can we deduplicate?
    pub exec fn read(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, r: Ghost<MemRegion>) -> (res: usize)
        requires
            old(tok)@.regions.contains_key(r@),
            r@.base == pbase,
            idx < 512,
            old(tok).inv(),
        ensures
            res == tok@.read(idx, r@),
            tok@ == old(tok)@,
            tok.inv(),
    {
        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        assert(core == tok.tok.consts().ult2core[tok.tok.thread()]);
        assert(tok.tok.consts().valid_core(core));
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            assert(tok.tok.st().core_states[core] is UnmapExecuting);
            mmu_tok.prophesy_read(addr);
            let post = os::State {
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };
            let read_result = mmu_tok.lbl()->Read_2;
            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(os::step_ReadPTMem(tok.tok.consts(), tok.tok.st(), post, core, addr, read_result, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::ReadPTMem { core, paddr: addr, value: read_result }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        let res = mmu::rl3::code::read(Tracked(&mut mmu_tok), addr);
        let ghost state2 = tok.tok.st();

        proof {
            broadcast use to_rl1::next_refines;
            assert(state1.mmu@.is_tso_read_deterministic(core, addr));
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let ghost state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(tok.inv());
        }
        res & MASK_NEG_DIRTY_ACCESS
    }

    pub exec fn write_stutter(
        Tracked(tok): Tracked<&mut Self>,
        pbase: usize,
        idx: usize,
        value: usize,
        Ghost(r): Ghost<MemRegion>,
        Ghost(root_pt1): Ghost<PTDir>,
        Ghost(root_pt2): Ghost<PTDir>,
    )
        requires
            old(tok)@.change_made,
            old(tok)@.regions.contains_key(r),
            r.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 0,
            old(tok)@.read(idx, r) & 1 == 1,
            PT::inv(old(tok)@, root_pt1),
            PT::inv(old(tok)@.write(idx, value, r, false), root_pt2),
            PT::interp_to_l0(old(tok)@.write(idx, value, r, false), root_pt2) == PT::interp_to_l0(old(tok)@, root_pt1),
        ensures
            tok@ == old(tok)@.write(idx, value, r, false),
            tok.inv(),
    {
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);

        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            old(tok)@.lemma_interps_match(root_pt1);
            old(tok).lemma_regions_derived_from_view_after_write(r, idx, value, false);
            old(tok)@.write(idx, value, r, false).lemma_interps_match(root_pt2);
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            let post = os::State { mmu: mmu_tok.post(), ..tok.tok.st() };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().common, mmu::rl1::Step::WriteNonpos, mmu_tok.lbl()));
            assert(os::step_UnmapOpStutter(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::UnmapOpStutter { core, paddr: addr, value }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
        let ghost state2 = tok.tok.st();

        proof {
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(unchanged_state_during_concurrent_trs(state2, state3, core));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            assert(tok.inv());
            assert(tok.tok.st().core_states[core] == old(tok).tok.st().core_states[core]);
            assert(tok@.regions[r] =~= old(tok)@.regions[r].update(idx as int, value));
            assert(tok@.regions[r] == tok@.regions[r].update(idx as int, value));
            assert(tok@.regions =~= old(tok)@.regions.insert(r, tok@.regions[r].update(idx as int, value)));
        }
    }

    pub exec fn write_change(
        Tracked(tok): Tracked<&mut Self>,
        pbase: usize,
        idx: usize,
        value: usize,
        Ghost(r): Ghost<MemRegion>,
        Ghost(root_pt): Ghost<PTDir>
    )
        requires
            !old(tok)@.change_made,
            old(tok)@.regions.contains_key(r),
            r.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 0,
            old(tok)@.read(idx, r) & 1 == 1,
            PT::interp_to_l0(old(tok)@, root_pt).contains_key(old(tok)@.args->Unmap_base as nat),
            PT::inv(old(tok)@, root_pt),
            PT::inv(old(tok)@.write(idx, value, r, true), root_pt),
            PT::interp_to_l0(old(tok)@.write(idx, value, r, true), root_pt)
                == PT::interp_to_l0(old(tok)@, root_pt).remove(old(tok)@.args->Unmap_base as nat),
        ensures
            tok@ == old(tok)@.write(idx, value, r, true),
            tok.inv(),
    {
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);

        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        //assert(core == tok.tok.core());
        let ghost vaddr = tok.tok.st().core_states[core]->UnmapExecuting_vaddr as usize;
        let ghost pte = PT::interp_to_l0(tok@, root_pt)[old(tok)@.args->Unmap_base as nat];
        proof {
            assert(tok.tok.st().core_states[core] == os::CoreState::UnmapExecuting { vaddr: vaddr as nat, ult_id: tok.tok.thread(), result: None });
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            let new_cs = os::CoreState::UnmapExecuting { ult_id: tok.tok.thread(), vaddr: vaddr as nat, result: Some(Ok((pte))) };
            let post = os::State {
                core_states: tok.tok.st().core_states.insert(core, new_cs),
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().common, mmu::rl1::Step::WriteNonpos, mmu_tok.lbl()));
            old(tok)@.lemma_interps_match(root_pt);
            old(tok).lemma_regions_derived_from_view_after_write(r, idx, value, true);
            old(tok)@.write(idx, value, r, true).lemma_interps_match(root_pt);
            assert(pte == tok.orig_st.interp_pt_mem()[vaddr as nat]);
            assert(os::step_UnmapOpChange(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::UnmapOpChange { core, paddr: addr, value }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
        let ghost state2 = tok.tok.st();
        proof { tok.change_made = true; }

        proof {
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(unchanged_state_during_concurrent_trs(state2, state3, core));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            assert(tok.inv());
        }
        assert(tok@.regions[r] =~= old(tok)@.regions[r].update(idx as int, value));
        assert(tok@.pt_mem == old(tok)@.pt_mem.write(add(r.base as usize, mul(idx, 8)), value));
        assert(tok@.regions =~= old(tok)@.regions.insert(r, old(tok)@.regions[r].update(idx as int, value)));
        assert(tok@.result === Ok(()));
        assert(tok@ =~= old(tok)@.write(idx, value, r, true));
    }

    pub exec fn deallocate(Tracked(tok): Tracked<&mut Self>, layer: usize, region: MemRegionExec)
        requires
            old(tok)@.regions.contains_key(region@),
            old(tok)@.regions[region@] === seq![0; 512],
            old(tok).inv(),
        ensures
            tok@.regions === old(tok)@.regions.remove(region@),
            tok@.pt_mem == old(tok)@.pt_mem,
            tok@.args == old(tok)@.args,
            tok@.orig_st == old(tok)@.orig_st,
            tok@.change_made == old(tok)@.change_made,
            tok.inv(),
    {
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut osext_tok = tok.tok.get_osext_token();
        proof {
            assert forall|pa: usize|
                aligned(pa as nat, 8) && region@.contains(pa as nat)
                    implies
                #[trigger] state1.mmu@.pt_mem.read(pa) == 0
            by {
                let i = (pa - region@.base) / 8;
                assert(0 <= i < 512);
                assert(old(tok)@.regions[region@][i as int] == state1.mmu@.pt_mem.read((region@.base + i * 8) as usize));
            };

            osext_tok.prophesy_deallocate(region);
            let post = os::State { os_ext: osext_tok.post(), ..tok.tok.st() };
            assert(old(tok)@.pt_mem == tok.tok.st().mmu@.pt_mem);
            assert(os::step_Deallocate(tok.tok.consts(), tok.tok.st(), post, core, region@, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::Deallocate { core, reg: region@ }, RLbl::Tau));
            tok.tok.register_internal_step_osext(&mut osext_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        os_ext::code::deallocate(Tracked(&mut osext_tok), region, layer);
        let ghost state2 = tok.tok.st();

        proof {
            tok.tok.return_osext_token(osext_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let ghost state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
        }
        assert(tok@.regions =~= old(tok)@.regions.remove(region@));
    }

    // TODO: duplicated from WrappedMapToken
    pub proof fn lemma_regions_derived_from_view_after_write(self, r: MemRegion, idx: usize, value: usize, change: bool)
        requires
            self.inv(),
            self@.regions.contains_key(r),
            idx < 512,
        ensures
            self@.write(idx, value, r, change).regions_derived_from_view()
    {
        let self_write = self@.write(idx, value, r, change);
        assert forall|r2| self_write.regions.contains_key(r2)
            implies
            #[trigger] self_write.regions[r2] =~= Seq::new(512, |i: int| self_write.pt_mem.mem[(r2.base + i * 8) as usize])
        by {
        };
    }

    /// Completes the remaining unmap transitions and performs a shootdown if necessary.
    pub exec fn finish_unmap_and_release_lock(Tracked(tok): Tracked<WrappedUnmapToken>, shootdown: DoShootdown, Ghost(root_pt): Ghost<PTDir>) -> (rtok: Tracked<Token>)
        requires
            (if shootdown is Yes {
                &&& tok@.change_made
                &&& shootdown->Yes_vaddr == tok@.args->Unmap_base
            } else {
                &&& !tok@.change_made
                &&& PT::inv(tok@, root_pt)
                &&& !PT::interp_to_l0(tok@, root_pt).contains_key(tok@.args->Unmap_base as nat)
            }),
            tok.inv(),
            forall|wtok: WrappedTokenView| ({
                &&& wtok.pt_mem == tok@.pt_mem
                &&& wtok.regions.dom() == tok@.regions.dom()
                &&& #[trigger] wtok.regions_derived_from_view()
            }) ==> exists|pt| PT::inv_and_nonempty(wtok, pt),
        ensures
            rtok@.progress() is Unready,
            rtok@.steps() === seq![],
            rtok@.steps_taken().last()->UnmapEnd_result == (if shootdown is Yes { Ok(()) } else { Err(()) }),
    {
        let ghost core = tok.tok.core();
        let tracked mut tok = tok;
        let ghost state1 = tok.tok.st();
        let ghost vaddr = tok.tok.st().core_states[core]->UnmapExecuting_vaddr;
        let ghost result = tok.tok.st().core_states[core]->UnmapExecuting_result;

        if let DoShootdown::Yes { vaddr, size } = shootdown {
            assert(result matches Some(Ok(_)));

            let tracked mut mmu_tok = tok.tok.get_mmu_token();
            proof {
                mmu_tok.prophesy_barrier();
                let post = os::State {
                    mmu: mmu_tok.post(),
                    ..tok.tok.st()
                };
                assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
                assert(os::step_Barrier(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
                assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::Barrier { core }, RLbl::Tau));
                tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
                os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
            }

            // Execute barrier to make writes globally visible
            mmu::rl3::code::barrier(Tracked(&mut mmu_tok));
            let ghost state2 = tok.tok.st();

            proof {
                broadcast use to_rl1::next_refines;
                tok.tok.return_mmu_token(mmu_tok);
                let pidx = tok.tok.do_concurrent_trs();
                lemma_concurrent_trs(state2, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
            }
            let ghost state3 = tok.tok.st();

            let tracked mut osext_tok = tok.tok.get_osext_token();
            proof {
                osext_tok.prophesy_init_shootdown(vaddr);
                let new_cs = os::CoreState::UnmapShootdownWaiting { ult_id: tok.tok.thread(), vaddr: vaddr as nat, result: result->Some_0 };
                let post = os::State {
                    core_states: tok.tok.st().core_states.insert(core, new_cs),
                    os_ext: osext_tok.post(),
                    ..tok.tok.st()
                };
                assert(os_ext::next(tok.tok.st().os_ext, post.os_ext, tok.tok.consts().common, osext_tok.lbl()));
                assert(os::step_UnmapInitiateShootdown(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
                assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::UnmapInitiateShootdown { core }, RLbl::Tau));
                tok.tok.register_internal_step_osext(&mut osext_tok, post);
                os_invariant::next_preserves_inv(tok.tok.consts(), state3, tok.tok.st(), RLbl::Tau);
            }

            // Initiate shootdown
            os_ext::code::init_shootdown(Tracked(&mut osext_tok), vaddr, size);
            let ghost state4 = tok.tok.st();

            proof {
                broadcast use to_rl1::next_refines;
                tok.tok.return_osext_token(osext_tok);
                let pidx = tok.tok.do_concurrent_trs();
                lemma_concurrent_trs(state4, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
            }

            let ghost state5 = tok.tok.st();

            let tracked mut mmu_tok = tok.tok.get_mmu_token();
            proof {
                mmu_tok.prophesy_invlpg(vaddr);
                let post = os::State {
                    mmu: mmu_tok.post(),
                    ..tok.tok.st()
                };
                assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().common, mmu_tok.lbl()));
                assert(tok.tok.st().os_ext.shootdown_vec.open_requests.contains(core));
                assert(os::step_Invlpg(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
                assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::Invlpg { core }, RLbl::Tau));
                tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
                os_invariant::next_preserves_inv(tok.tok.consts(), state5, tok.tok.st(), RLbl::Tau);
            }

            // Note on the invlpg here:
            // For the Linux integration this invlpg isn't necessary but due to our modeling we
            // still need to do it. Our definition of concurrent transitions doesn't allow a local
            // `AckShootdownIPI` (or invlpg) to happen as a "concurrent" transition. This in turn
            // means we'd be able to prove that the post state given by the `WaitShootdown`
            // transition contradicts our knowledge (which would be consistent with that function
            // not terminating).

            // Execute invlpg to evict from local TLB
            mmu::rl3::code::invlpg(Tracked(&mut mmu_tok), vaddr);
            let ghost state6 = tok.tok.st();

            proof {
                broadcast use to_rl1::next_refines;
                tok.tok.return_mmu_token(mmu_tok);
                let pidx = tok.tok.do_concurrent_trs();
                lemma_concurrent_trs(state6, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
            }
            let ghost state7 = tok.tok.st();

            let tracked mut osext_tok = tok.tok.get_osext_token();
            proof {
                osext_tok.prophesy_ack_shootdown();
                let post = os::State {
                    os_ext: osext_tok.post(),
                    ..tok.tok.st()
                };
                assert(os_ext::next(tok.tok.st().os_ext, post.os_ext, tok.tok.consts().common, osext_tok.lbl()));
                assert(!tok.tok.st().mmu@.writes.nonpos.contains(core));
                assert(!tok.tok.st().mmu@.tlbs[core].contains_key(vaddr)) by {
                    assert(tok.tok.st().core_states[core] is UnmapShootdownWaiting);
                    assert(vaddr == tok.tok.st().core_states[core]->UnmapShootdownWaiting_vaddr);
                    // &&& post.os_ext.shootdown_vec.open_requests.subset_of(pre.os_ext.shootdown_vec.open_requests)
                    assert(state6.os_ext.shootdown_vec.open_requests.contains(core));
                    // assert(!tok.tok.st().os_ext.shootdown_vec.open_requests.contains(core));
                    broadcast use to_rl1::next_refines;
                        assert(!state6.mmu@.tlbs[core].contains_key(vaddr));
                };
                // assert(vaddr == tok.tok.st().os_ext.shootdown_vec.vaddr);
                assert(os::step_AckShootdownIPI(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
                assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::AckShootdownIPI { core }, RLbl::Tau));
                tok.tok.register_internal_step_osext(&mut osext_tok, post);
                os_invariant::next_preserves_inv(tok.tok.consts(), state7, tok.tok.st(), RLbl::Tau);
            }

            // Initiate shootdown
            os_ext::code::ack_shootdown(Tracked(&mut osext_tok));
            let ghost state8 = tok.tok.st();

            proof {
                broadcast use to_rl1::next_refines;
                tok.tok.return_osext_token(osext_tok);
                let pidx = tok.tok.do_concurrent_trs();
                lemma_concurrent_trs(state8, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
            }

            let ghost state9 = tok.tok.st();

            let tracked mut osext_tok = tok.tok.get_osext_token();
            proof {
                osext_tok.prophesy_wait_shootdown();
                let post = state9; // read-only step
                assert(os_ext::next(tok.tok.st().os_ext, post.os_ext, tok.tok.consts().common, osext_tok.lbl()));
                assert(os::step_UnmapWaitShootdown(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
                assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::UnmapWaitShootdown { core }, RLbl::Tau));
                tok.tok.register_internal_step_osext(&mut osext_tok, post);
            }

            // Wait for completion of shootdown
            os_ext::code::wait_shootdown(Tracked(&mut osext_tok));
            let ghost state10 = tok.tok.st();

            proof {
                broadcast use to_rl1::next_refines;
                tok.tok.return_osext_token(osext_tok);
                let pidx = tok.tok.do_concurrent_trs();
                lemma_concurrent_trs(state10, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
            }

            assert(state10.os_ext.shootdown_vec.open_requests.is_empty());
            assert(tok.tok.st().mmu@.writes.tso === set![]);
            assert(tok.tok.st().mmu@.writes.nonpos =~= set![]);
        } else {
            // register fail
            assert(result is None);

            proof {
                tok@.lemma_interps_match(root_pt);
                let new_cs = os::CoreState::UnmapOpDone { ult_id: tok.tok.thread(), vaddr: vaddr as nat, result: Err(()) };
                let post = os::State {
                    core_states: tok.tok.st().core_states.insert(core, new_cs),
                    ..tok.tok.st()
                };

                assert(os::step_UnmapOpFail(tok.tok.consts(), tok.tok.st(), post, core, RLbl::Tau));
                assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::UnmapOpFail { core }, RLbl::Tau));
                tok.tok.register_internal_step(post);
                os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
                let ghost state2 = tok.tok.st();
                let pidx = tok.tok.do_concurrent_trs();
                lemma_concurrent_trs(state2, tok.tok.st(), tok.tok.consts(), tok.tok.core(), pidx);
                assert(tok.tok.st().mmu@.writes.tso === set![]);
                assert(tok.tok.st().mmu@.writes.nonpos === set![]);
            }
        }

        let tracked mut osext_tok = tok.tok.get_osext_token();

        proof {
            let ghost statex1 = tok.tok.st();

            let cs = tok.tok.st().core_states[core];
            let result = if cs is UnmapShootdownWaiting { Ok(()) } else { Err(()) };

            broadcast use to_rl1::next_refines;
            osext_tok.prophesy_release_lock();
            let post = os::State {
                core_states: tok.tok.st().core_states.insert(core, os::CoreState::Idle),
                os_ext: osext_tok.post(),
                ..tok.tok.st()
            };
            assert(os_ext::step_ReleaseLock(tok.tok.st().os_ext, post.os_ext, tok.tok.consts().common, osext_tok.lbl()));
            let lbl = RLbl::UnmapEnd { thread_id: tok.tok.thread(), vaddr, result };

            assert(post.inv_impl()) by {
                assert(tok.tok.st().mmu@.pt_mem == tok@.pt_mem);
                assert(tok.tok.st().os_ext.allocated == tok@.regions.dom());
            };
            assert(tok.tok.st().mmu@.pending_unmaps === map![]);
            assert(os::step_UnmapEnd(tok.tok.consts(), tok.tok.st(), post, core, lbl));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::UnmapEnd { core }, lbl));
            tok.tok.register_external_step_osext(&mut osext_tok, post, lbl);
            os_invariant::next_preserves_inv(tok.tok.consts(), statex1, tok.tok.st(), lbl);
        }

        os_ext::code::release_lock(Tracked(&mut osext_tok));

        proof {
            broadcast use to_rl1::next_refines;
            tok.tok.return_osext_token(osext_tok);
            assert(tok.tok.steps() === seq![]);
        }

        Tracked(tok.tok)
    }
}

pub enum DoShootdown {
    Yes { vaddr: usize, size: usize },
    No,
}

pub exec fn start_unmap_and_acquire_lock(Tracked(tok): Tracked<&mut Token>, Ghost(vaddr): Ghost<nat>)
    requires
        os::step_Unmap_enabled(vaddr),
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).consts().valid_core(old(tok).core()), // TODO: ??
        old(tok).st().core_states[old(tok).core()] is Idle,
        old(tok).steps_taken() === seq![],
        old(tok).steps().len() == 2,
        old(tok).steps().first() == (RLbl::UnmapStart { thread_id: old(tok).thread(), vaddr }),
        old(tok).progress() is Unready,
        old(tok).st().inv(old(tok).consts()),
    ensures
        tok.core() == old(tok).core(),
        tok.thread() == old(tok).thread(),
        tok.st().core_states[tok.core()] == (os::CoreState::UnmapExecuting { ult_id: tok.thread(), vaddr, result: None }),
        tok.progress() is Ready,
        tok.st().os_ext.lock == Some(tok.core()),
        tok.st().inv(tok.consts()),
        tok.st().mmu@.pt_mem.pml4 == old(tok).st().mmu@.pt_mem.pml4,
        tok.consts() == old(tok).consts(),
        tok.steps() == old(tok).steps().drop_first(),
        tok.steps_taken() == seq![old(tok).steps().first()],
        !tok.on_first_step(),
        // From `inv_impl`:
        forall|wtok: wrapped_token::WrappedTokenView| ({
            &&& wtok.pt_mem == tok.st().mmu@.pt_mem
            &&& wtok.regions.dom() == tok.st().os_ext.allocated
            &&& #[trigger] wtok.regions_derived_from_view()
        }) ==> exists|pt| PT::inv_and_nonempty(wtok, pt),
{
    let ghost state1 = tok.st();
    let ghost core = tok.core();
    let ghost pidx = tok.do_concurrent_trs();
    let ghost state2 = tok.st();
    proof {
        lemma_concurrent_trs_no_lock(state1, state2, tok.consts(), core, pidx);
        let new_cs = os::CoreState::UnmapWaiting { ult_id: tok.thread(), vaddr };
        let pte_size = if state2.interp_pt_mem().contains_key(vaddr) { state2.interp_pt_mem()[vaddr].frame.size } else { 0 };
        let new_sound = tok.st().sound && os::step_Unmap_sound(tok.st(), vaddr, pte_size);
        let post = os::State {
            core_states: tok.st().core_states.insert(core, new_cs),
            sound: new_sound,
            ..tok.st()
        };
        let lbl = RLbl::UnmapStart { thread_id: tok.thread(), vaddr };
        assert(os::step_UnmapStart(tok.consts(), tok.st(), post, core, lbl));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::UnmapStart { core }, lbl));
        tok.register_external_step(post, lbl);
        let state3 = tok.st();
        os_invariant::next_preserves_inv(tok.consts(), state2, state3, lbl);
        let ghost pidx = tok.do_concurrent_trs();
        let state4 = tok.st();
        lemma_concurrent_trs_no_lock(state3, state4, tok.consts(), core, pidx);
    }


    let ghost state5 = tok.st();
    assert(core == tok.consts().ult2core[tok.thread()]);
    let tracked mut osext_tok = tok.get_osext_token();
    proof {
        osext_tok.prophesy_acquire_lock();
        let vaddr = tok.st().core_states[core]->UnmapWaiting_vaddr;
        let new_cs = os::CoreState::UnmapExecuting { ult_id: tok.thread(), vaddr, result: None };
        let post = os::State {
            core_states: tok.st().core_states.insert(core, new_cs),
            os_ext: osext_tok.post(),
            ..tok.st()
        };
        assert(os_ext::step_AcquireLock(tok.st().os_ext, post.os_ext, tok.consts().common, osext_tok.lbl()));
        assert(os::step_UnmapOpStart(tok.consts(), tok.st(), post, core, RLbl::Tau));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::UnmapOpStart { core }, RLbl::Tau));
        tok.register_internal_step_osext(&mut osext_tok, post);
        os_invariant::next_preserves_inv(tok.consts(), state5, tok.st(), RLbl::Tau);
    }

    os_ext::code::acquire_lock(Tracked(&mut osext_tok));
    let ghost state6 = tok.st();

    proof {
        tok.return_osext_token(osext_tok);
        let pidx = tok.do_concurrent_trs();
        let state7 = tok.st();
        lemma_concurrent_trs(state6, state7, tok.consts(), tok.core(), pidx);
    }
}

} // verus!
