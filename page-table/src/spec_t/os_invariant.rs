use vstd::prelude::*;
use vstd::assert_by_contradiction;

//use crate::impl_u::spec_pt;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    candidate_mapping_overlaps_existing_vmem, overlap, MemRegion, PTE, Core, X86_NUM_ENTRIES,
    new_seq, aligned, MAX_BASE, x86_arch_spec_upper_bound, candidate_mapping_in_bounds_pmem,
    L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE
};
#[cfg(verus_keep_ghost)]
use crate::definitions_u::{ lemma_new_seq };
use crate::spec_t::{hlspec, os};
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::mmu;
use crate::theorem::RLbl;
use crate::impl_u::wrapped_token;
use crate::impl_u::l2_impl::{ PTDir, PT };
use crate::spec_t::mmu::rl1;

verus! {

pub proof fn lemma_init_implies_empty_map(s: os::State, c: os::Constants)
    requires os::init(c, s),
    ensures s.interp_pt_mem() === map![]
{
    reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
    assert forall|vaddr| #[trigger] s.mmu@.pt_mem.pt_walk(vaddr).result() is Invalid by {
        crate::impl_u::l2_impl::lemma_bitvector_facts_simple();
        crate::spec_t::mmu::translation::lemma_bit_indices_less_512(vaddr);
    };
    assert(s.interp_pt_mem() =~= map![]);
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Proof of Invariant
///////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_inv(c: os::Constants, s: os::State)
    requires os::init(c, s),
    ensures s.inv(c),
{
    to_rl1::init_implies_inv(s.mmu, c.common);
    to_rl1::init_refines(s.mmu, c.common);
    assert(s.inv_impl()) by {
        assert forall|wtok: wrapped_token::WrappedTokenView| ({
            &&& wtok.pt_mem == s.mmu@.pt_mem
            &&& wtok.regions.dom() == s.os_ext.allocated
            &&& #[trigger] wtok.regions_derived_from_view()
        })
            implies exists|pt| PT::inv_and_nonempty(wtok, pt)
        by {
            let pml4 = s.mmu@.pt_mem.pml4;
            let region = MemRegion { base: pml4 as nat, size: 4096 };
            let pt =
                PTDir {
                    region,
                    entries: new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None),
                    used_regions: set![region],
                };
            lemma_new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None);
            assert forall|i: usize| 0 <= i < 512 implies wtok.regions[region][i as int] == 0 by {
                assert(s.mmu@.pt_mem.read(add(pml4, mul(i, 8))) == 0);
            };
            PT::lemma_zeroed_page_implies_empty_at(wtok, pt, 0, pml4);
            assert(PT::inv_and_nonempty(wtok, pt));
        };
    };

    lemma_init_implies_empty_map(s, c);
    assert(s.inv_basic(c));
    init_implies_tlb_inv(c, s);
}

pub proof fn next_preserves_inv(c: os::Constants, s1: os::State, s2: os::State, lbl: RLbl)
    requires
        s1.inv(c),
        os::next(c, s1, s2, lbl),
    ensures
        s2.inv(c),
{
    let step = choose|step| os::next_step(c, s1, s2, step, lbl);
    next_step_preserves_inv(c, s1, s2, step, lbl);
}

#[verifier::rlimit(100)] #[verifier(spinoff_prover)]
pub proof fn next_step_preserves_inv(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    /*
     assert(s2.inv_successful_maps(c)) by {
        assert forall|core| c.valid_core(core) implies {
            match s2.core_states[core] {
                os::CoreState::UnmapExecuting { vaddr, result: Some(_),.. }
                | os::CoreState::UnmapOpDone { vaddr, .. }
                | os::CoreState::UnmapShootdownWaiting { vaddr, .. }
                    => !s2.interp_pt_mem().dom().contains(vaddr),
                _ => true,
            }
        } by { let _ = s1.core_states[core].is_in_crit_sect(); }
    };
    */

    assert(s2.inv_basic(c));
    next_step_preserves_inv_mmu(c, s1, s2, step, lbl);
    next_step_preserves_inv_allocated_mem(c, s1, s2, step, lbl);
    next_step_preserves_overlap_mem_inv(c, s1, s2, step, lbl);
    next_step_preserves_inv_impl(c, s1, s2, step, lbl);
    next_step_preserves_inv_writes(c, s1, s2, step, lbl);
    next_step_preserves_inv_shootdown(c, s1, s2, step, lbl);
    next_step_preserves_inv_pending_maps(c, s1, s2, step, lbl);
    next_step_preserves_tlb_inv(c, s1, s2, step, lbl);
}

pub proof fn next_step_preserves_inv_mmu(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv_basic(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_mmu(c),
{
    x86_arch_spec_upper_bound();
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    assert(s2.mmu@.pt_mem.mem.dom() =~= s1.mmu@.pt_mem.mem.dom());
    assert(s1.mmu@.phys_mem.len() == c.common.range_mem.1);
    match step {
        os::Step::MemOp { core } => {
            let vaddr = lbl->MemOp_vaddr;
            let op = lbl->MemOp_op;
            assert(mmu::rl3::next(s1.mmu, s2.mmu, c.common, mmu::Lbl::MemOp(core, vaddr as usize, op)));
            let mmu_step = choose|step| #[trigger] mmu::rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mmu::Lbl::MemOp(core, vaddr as usize, op));
            assert(mmu::rl1::next_step(s1.mmu@, s2.mmu@, c.common, mmu_step, mmu::Lbl::MemOp(core, vaddr as usize, op)));
            if mmu_step is MemOpTLB {
                let tlb_va = mmu_step->MemOpTLB_tlb_va;
                let pte = s1.mmu@.tlbs[core][tlb_va];
                let paddr = pte.frame.base + (vaddr - tlb_va);
                assert(s2.inv_mapped_pte_wf(c));
                assert(s1.mmu@.tlbs[core].dom().map(|v| v as nat).contains(tlb_va as nat));
                assert(c.valid_core(core));
                assert(candidate_mapping_in_bounds_pmem(c.common, pte));
                assert(pte.frame.size == L1_ENTRY_SIZE
                        || pte.frame.size == L2_ENTRY_SIZE
                        || pte.frame.size == L3_ENTRY_SIZE);
                assert(aligned(tlb_va as nat, pte.frame.size));
                assert(vaddr as int + op.op_size() as int <= tlb_va + pte.frame.size) by {
                    assert(pte.frame.size == L1_ENTRY_SIZE
                        || pte.frame.size == L2_ENTRY_SIZE
                        || pte.frame.size == L3_ENTRY_SIZE);
                    assert(aligned(vaddr, op.op_size()));
                    assert(vaddr + op.op_size() <= tlb_va + pte.frame.size) by (nonlinear_arith)
                        requires vaddr < tlb_va + pte.frame.size,
                          pte.frame.size == 4096 || pte.frame.size == 512 * 4096
                              || pte.frame.size == 512 * (512 * 4096),
                          op.op_size() == 1 || op.op_size() == 2 || op.op_size() == 4 || op.op_size() == 8,
                          vaddr % op.op_size() == 0,
                          aligned(tlb_va as nat, pte.frame.size);
                }
            }
            assert(s2.mmu@.phys_mem.len() == s1.mmu@.phys_mem.len());
            assert(s2.inv_mmu(c));
        }
        _ => {},
    }
}

pub proof fn next_step_preserves_inv_pending_maps(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_pending_maps(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        // Map steps
        os::Step::MMU => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::MemOp { core } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::ReadPTMem { core, paddr, value } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::Barrier { core } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::Invlpg { core } => {
            assert(s2.inv_pending_maps(c));
        }

        os::Step::MapStart { core } => {
            assert forall |base| #[trigger] s2.mmu@.pending_maps.dom().contains(base) implies
                exists |core| os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps)
            by {
                assert(s1.mmu@.pending_maps.dom().contains(base));
                let core = choose |core| os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps);
                assert(os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps));
                assert(os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps));
            }
            assert(s2.inv_pending_maps(c));
        },
        os::Step::MapOpStart { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::Allocate { core, res } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::MapOpStutter { core, paddr, value }
        | os::Step::UnmapOpChange { core, paddr, value }
        | os::Step::UnmapOpStutter { core, paddr, value } => {
            let mlbl = mmu::Lbl::Write(core, paddr, value);
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mlbl);
            assert(rl1::next_step(s1.mmu@, s2.mmu@, c.common, mmu_step, mlbl));
            match mmu_step {
                rl1::Step::WriteNonneg => {
                    assert forall |vbase| s2.mmu@.pt_mem@.contains_key(vbase) implies s1.mmu@.pt_mem@.contains_key(vbase)
                    by {
                        assert(s2.interp_pt_mem().dom().contains(vbase as nat));
                        assert(s1.interp_pt_mem().dom().contains(vbase as nat));
                    }
                    assert(s1.mmu@.pending_maps =~= s2.mmu@.pending_maps);
                    assert(s2.inv_pending_maps(c));
                }
                rl1::Step::WriteNonpos => {
                    assert(s2.inv_pending_maps(c));
                }
                _ => {
                    assert(false);
                }
            }
        },
        os::Step::MapOpChange { core, paddr, value } => {
            let mlbl = mmu::Lbl::Write(core, paddr, value);
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mlbl);
            assert(rl1::next_step(s1.mmu@, s2.mmu@, c.common, mmu_step, mlbl));
            match mmu_step {
                rl1::Step::WriteNonneg => {
                    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
                    let pte = s1.core_states[core]->MapExecuting_pte;
                    assert forall |base| #[trigger] s2.mmu@.pending_maps.dom().contains(base) implies
                        exists |core1| os::State::is_pending_for_core(c, base, core1,
                            s2.core_states, s2.mmu@.pending_maps)
                    by {
                        if base == vaddr {
                            assert(s2.interp_pt_mem().dom().contains(base as nat));
                            assert(s2.interp_pt_mem()[base as nat] == pte);
                            assert(s2.mmu@.pending_maps.dom().contains(base));
                            assert(s2.mmu@.pending_maps[base] == pte);
                            assert(os::State::is_pending_for_core(c, base, core,
                                s2.core_states, s2.mmu@.pending_maps));
                        } else {
                            assert(s2.interp_pt_mem().dom().contains(base as nat));
                            assert(s1.interp_pt_mem().dom().contains(base as nat));
                            assert(s1.mmu@.pending_maps.dom().contains(base));

                            let core1 = choose |core1| os::State::is_pending_for_core(c, base, core1,
                                s1.core_states, s1.mmu@.pending_maps);
                            assert(os::State::is_pending_for_core(c, base, core1,
                                s1.core_states, s1.mmu@.pending_maps));
                            assert(os::State::is_pending_for_core(c, base, core1,
                                s2.core_states, s2.mmu@.pending_maps));
                        }
                    }
                    assert(s2.inv_pending_maps(c));
                }
                rl1::Step::WriteNonpos => {
                    assert(s2.inv_pending_maps(c));
                }
                _ => {
                    assert(false);
                }
            }
        },
        os::Step::MapNoOp { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::MapEnd { core } => {
            assert(s2.inv_pending_maps(c));
        },

        //Unmap steps
        os::Step::UnmapStart { core } => {
            assert forall |base| #[trigger] s2.mmu@.pending_maps.dom().contains(base) implies
                exists |core| os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps)
            by {
                assert(s1.mmu@.pending_maps.dom().contains(base));
                let core = choose |core| os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps);
                assert(os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps));
                assert(os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps));
            }
            assert(s2.inv_pending_maps(c));
        },
        os::Step::UnmapOpStart { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::Deallocate { core: Core, reg: MemRegion } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::UnmapOpFail { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::UnmapWaitShootdown { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::AckShootdownIPI { core: Core } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::UnmapEnd { core: Core } => {
            assert(s2.inv_pending_maps(c));
        }
    }
}

pub proof fn next_step_preserves_inv_allocated_mem(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_allocated_mem(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        os::Step::MapOpStart { core } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
        },
        os::Step::Allocate { core, res } => {
            assert forall|pa: usize|
                aligned(pa as nat, 8)
                && c.common.in_ptmem_range(pa as nat, 8)
                && #[trigger] s2.mmu@.pt_mem.read(pa) != 0
                    implies
                exists|r| #[trigger] s2.os_ext.allocated.contains(r) && r.contains(pa as nat)
            by {
                assert(s1.mmu@.pt_mem.read(pa) != 0);
                let r = choose|r| #[trigger] s1.os_ext.allocated.contains(r) && r.contains(pa as nat);
                assert(s2.os_ext.allocated.contains(r));
            };
        },
        os::Step::MapOpStutter { core, paddr, value } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
            assert(forall|pa| pa != paddr ==> s2.mmu@.pt_mem.read(pa) == s1.mmu@.pt_mem.read(pa));
        },
        os::Step::MapOpChange { core, paddr, value } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
            assert(forall|pa| pa != paddr ==> s2.mmu@.pt_mem.read(pa) == s1.mmu@.pt_mem.read(pa));
        },
        os::Step::MapEnd { core } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
        },
        os::Step::UnmapOpStart { core } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
        },
        os::Step::Deallocate { core, reg } => {
            assert forall|pa: usize|
                aligned(pa as nat, 8)
                && c.common.in_ptmem_range(pa as nat, 8)
                && #[trigger] s2.mmu@.pt_mem.read(pa) != 0
                    implies
                exists|r| #[trigger] s2.os_ext.allocated.contains(r) && r.contains(pa as nat)
            by {
                if s2.mmu@.pt_mem.read(pa) != 0 {
                    assert(s1.mmu@.pt_mem.read(pa) != 0);
                    assert(exists|r| #[trigger] s1.os_ext.allocated.contains(r) && r.contains(pa as nat));
                    let r = choose|r| #[trigger] s1.os_ext.allocated.contains(r) && r.contains(pa as nat);
                    if r != reg {
                        assert(s2.os_ext.allocated.contains(r));
                    }
                }
            };
        },
        os::Step::UnmapOpChange { core, paddr, value } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
            assert(forall|pa| pa != paddr ==> s2.mmu@.pt_mem.read(pa) == s1.mmu@.pt_mem.read(pa));
        },
        os::Step::UnmapOpStutter { core, paddr, value } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
            assert(forall|pa| pa != paddr ==> s2.mmu@.pt_mem.read(pa) == s1.mmu@.pt_mem.read(pa));
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
        },
        os::Step::AckShootdownIPI { core } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
        },
        os::Step::UnmapEnd { core } => {
            assert(s2.os_ext.allocated == s1.os_ext.allocated);
        },
        _ => {},
    }
}

pub proof fn next_step_preserves_inv_impl(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv_mmu(c),
        s1.inv_lock(c),
        s1.inv_impl(),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_impl(),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
}

pub proof fn next_step_preserves_inv_shootdown(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_shootdown(c),
{
    reveal(mmu::Constants::valid_core);
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
}

pub proof fn next_step_preserves_inv_writes(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_writes(c),
{
    hide(os::State::tlb_inv);
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        os::Step::Invlpg { core } => {
            assert((s2.os_ext.lock matches Some(core) && s2.core_states[core].is_mapping())
                ==> s2.mmu@.writes.nonpos === set![]);
            assert(s2.os_ext.lock is None ==> {
                &&& s2.mmu@.writes.tso === set![]
                &&& s2.mmu@.writes.nonpos === set![]
            });
            assert(s2.inv_writes(c));
        },
        os::Step::UnmapOpChange { core, paddr, value } => {
            // If I remove this match arm, Verus times out, wtf
        },
        _ => {},
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of TLB Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_tlb_inv(c: os::Constants, s: os::State)
    requires os::init(c, s),
    ensures s.tlb_inv(c),
{
    to_rl1::init_refines(s.mmu, c.common);
    assert(s.os_ext.shootdown_vec.open_requests.is_empty());
    Set::lemma_len0_is_empty(s.os_ext.shootdown_vec.open_requests);
    assert(s.os_ext.shootdown_vec.open_requests === Set::empty());
    assert(s.shootdown_cores_valid(c));
    assert(s.successful_IPI(c));
    assert(s.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
}

#[verifier::spinoff_prover]
pub proof fn next_step_preserves_tlb_inv(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    step: os::Step,
    lbl: RLbl,
)
    requires
        s1.tlb_inv(c),
        s1.inv_mmu(c),
        s1.inv_basic(c),
        s2.inv_basic(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.tlb_inv(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        os::Step::MMU => {
            assert(s2.shootdown_cores_valid(c));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(rl1::next(s1.mmu@, s2.mmu@, c.common, mmu::Lbl::Tau));
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mmu::Lbl::Tau);
            assert(s2.interp_pt_mem().dom().union(s2.unmap_vaddr_set())
                =~= s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set()));
            match mmu_step {
                rl1::Step::TLBFill { core, vaddr } => {
                    let vbase = s1.mmu@.pt_mem.pt_walk(vaddr).result()->Valid_vbase;
                    crate::spec_t::mmu::rl2::lemma_pt_walk_result_vbase_equal(s1.mmu@.pt_mem, vaddr);
                    assert(s2.shootdown_cores_valid(c));
                    assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                        <==> s1.is_unmap_vaddr_core(core, vaddr));
                    assert forall|dispatcher: Core, handler: Core|
                        #[trigger] c.valid_core(dispatcher)
                        && c.valid_core(handler)
                        && s2.core_states[dispatcher] is UnmapShootdownWaiting
                        && !(#[trigger] s2.mmu@.writes.nonpos.contains(handler))
                            implies
                        !s2.mmu@.tlbs[handler].contains_key((s2.core_states[dispatcher]->UnmapShootdownWaiting_vaddr) as usize)
                    by {
                        // assert(!s2.os_ext.shootdown_vec.open_requests.contains(handler));
                        let shootdown_vaddr = s2.core_states[dispatcher]->UnmapShootdownWaiting_vaddr;
                        if handler == core {
                            assert(s2.core_states[dispatcher] == s1.core_states[dispatcher]);
                            assert(s1.core_states[dispatcher].is_unmapping());
                            assert(shootdown_vaddr == s1.core_states[dispatcher].unmap_vaddr());
                            assert(!s2.interp_pt_mem().contains_key(shootdown_vaddr));
                            assert(shootdown_vaddr < MAX_BASE);
                            assert(!s2.mmu@.pt_mem@.contains_key(shootdown_vaddr as usize));
                            assert(!s1.mmu@.tlbs[handler].contains_key(shootdown_vaddr as usize));
                            if vbase == shootdown_vaddr {
                                reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
                                assert(!s2.mmu@.pt_mem.is_base_pt_walk(shootdown_vaddr as usize));
                                assert(!s1.mmu@.pt_mem.is_base_pt_walk(shootdown_vaddr as usize));
                                assert(s1.mmu@.pt_mem.is_base_pt_walk(shootdown_vaddr as usize));
                            } else {
                                assert(!s2.mmu@.tlbs[handler].contains_key(shootdown_vaddr as usize));
                            }
                        }
                    };
                    assert(s2.successful_invlpg(c));
                    assert(s2.successful_IPI(c));
                    assert forall|tlb_core: Core, tlb_va: nat| #![auto]
                        c.valid_core(tlb_core)
                        && s2.mmu@.tlbs[tlb_core].dom().map(|v| v as nat).contains(tlb_va)
                            implies
                        s2.interp_pt_mem().dom().union(s2.unmap_vaddr_set()).contains(tlb_va)
                    by {
                        if tlb_core == core {
                            if tlb_va == vbase {
                                reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
                                assert(s1.interp_pt_mem().contains_key(tlb_va));
                            } else {
                                assert(s1.mmu@.tlbs[tlb_core].dom().map(|v| v as nat).contains(tlb_va));
                                assert(s2.interp_pt_mem().dom().union(s2.unmap_vaddr_set()).contains(tlb_va)
                                    =~= s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set()).contains(tlb_va));
                            }
                        }
                    };
                    assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
                    assert(s2.TLB_interp_pt_mem_agree(c)) by {
                        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
                    }
                    assert(s2.TLB_unmap_agree(c)) by {
                        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
                    }
                }
                rl1::Step::TLBFillNA { core, vaddr } => {
                    assert(s2.successful_IPI(c));
                    assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
                    assert(s2.TLB_interp_pt_mem_agree(c));
                    assert(s2.TLB_unmap_agree(c));
                }
                _ => {
                    assert(forall|core| #![auto] s2.mmu@.tlbs[core].submap_of(s1.mmu@.tlbs[core]));
                    assert(s2.TLB_interp_pt_mem_agree(c));
                    assert(s2.TLB_unmap_agree(c));
                },
            }
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
        },
        os::Step::MapStart { core }
        | os::Step::UnmapStart { core }
        | os::Step::AckShootdownIPI { core } => {
            x86_arch_spec_upper_bound();
            assert(s1.unmap_vaddr_set() =~= s2.unmap_vaddr_set()) by {
                assert forall |vaddr| s1.is_unmap_vaddr(vaddr) implies
                    s2.is_unmap_vaddr(vaddr) by {
                        let unmap_core = choose|unmap_core| s1.is_unmap_vaddr_core(unmap_core, vaddr);
                        assert(s2.is_unmap_vaddr_core(unmap_core, vaddr));
                    }
                assert forall |vaddr| s2.is_unmap_vaddr(vaddr) implies
                    s1.is_unmap_vaddr(vaddr) by {
                        let unmap_core = choose|unmap_core| s2.is_unmap_vaddr_core(unmap_core, vaddr);
                        assert(s1.is_unmap_vaddr_core(unmap_core, vaddr));
                    }
            }
            assert(s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set()) =~= s2.interp_pt_mem().dom().union(s2.unmap_vaddr_set()));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(s2.tlb_inv(c));
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s2.shootdown_cores_valid(c));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(s1.mmu@.writes.nonpos == Set::new(|core| c.valid_core(core)));
            assert(s2.successful_invlpg(c));
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
            assert(s2.TLB_interp_pt_mem_agree(c));
            assert(s2.TLB_unmap_agree(c));
        },
        os::Step::Invlpg { core, .. } => {
            assert(s2.all_cores_nonpos_before_shootdown(c));
            assert(s2.shootdown_cores_valid(c));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(s2.successful_invlpg(c));
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
            assert(s2.TLB_interp_pt_mem_agree(c));
            assert(s2.TLB_unmap_agree(c));
        }
        os::Step::MemOp { core }
        | os::Step::ReadPTMem { core, .. }
        | os::Step::Barrier { core }
        | os::Step::MapOpStart { core }
        | os::Step::Allocate { core, .. }
        | os::Step::MapNoOp { core }
        | os::Step::MapEnd { core }
        | os::Step::UnmapOpStart { core }
        | os::Step::UnmapWaitShootdown { core }
        | os::Step::Deallocate { core, .. }
        | os::Step::UnmapOpFail { core }
        | os::Step::MapOpStutter { core, .. } => {
            assert(s2.shootdown_cores_valid(c));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(s2.successful_invlpg(c));
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
            assert(s2.TLB_interp_pt_mem_agree(c));

            assert(s2.TLB_unmap_agree(c));
        },
        os::Step::MapOpChange { core, .. } => {
            assert(s2.shootdown_cores_valid(c));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(s2.successful_invlpg(c));
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
            assert(s2.TLB_interp_pt_mem_agree(c)) by {
                assert forall|tlb_core: Core, v: usize|
                    #[trigger] c.valid_core(tlb_core)
                    && #[trigger] s2.mmu@.tlbs[tlb_core].dom().contains(v)
                    && s2.interp_pt_mem().dom().contains(v as nat)
                        implies
                    s2.mmu@.tlbs[tlb_core][v] == s2.interp_pt_mem()[v as nat]
                by {
                    assert(s1.mmu@.tlbs[tlb_core].dom().contains(v));
                    assert(s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set()).contains(v as nat));
                    assert_by_contradiction!(!s1.unmap_vaddr_set().contains(v as nat), {
                        let unmap_core = choose|core: Core| s1.is_unmap_vaddr_core(core, v as nat);
                    });
                };
            };


            assert(s2.TLB_unmap_agree(c));
        },
        //unmap steps
        os::Step::UnmapOpChange { core, paddr, value } => {
            assert(s2.all_cores_nonpos_before_shootdown(c)) by {
                assert(s2.mmu@.writes.nonpos =~= Set::new(|core| c.valid_core(core)));
            };
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            let unmapped_vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
            let unmapped_pte = s1.interp_pt_mem()[unmapped_vaddr];
            assert(unmapped_vaddr <= usize::MAX);
            assert(s2.mmu@.pending_unmaps =~= s1.mmu@.pending_unmaps.insert(unmapped_vaddr as usize, unmapped_pte)) by {
                assert forall|va| s2.mmu@.pending_unmaps.contains_key(va) && !s1.mmu@.pending_unmaps.contains_key(va)
                    implies va == unmapped_vaddr
                by {
                    assert(s1.mmu@.pt_mem@.contains_key(va));
                    assert(!s2.mmu@.pt_mem@.contains_key(va));
                    assert(s1.interp_pt_mem().contains_key(va as nat));
                    assert(!s2.interp_pt_mem().contains_key(va as nat));
                };
            };
            assert(s2.is_unmap_vaddr_core(core, unmapped_vaddr));
            assert(s2.interp_pt_mem() =~= s1.interp_pt_mem().remove(unmapped_vaddr));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
        },
        os::Step::UnmapOpStutter { core, paddr, value } => {
            assert(s2.all_cores_nonpos_before_shootdown(c)) by {
                assert(s2.mmu@.writes.nonpos =~= s1.mmu@.writes.nonpos);
            };
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assert(forall|core, vaddr: nat| s2.is_unmap_vaddr_core(core, vaddr)
                <==> s1.is_unmap_vaddr_core(core, vaddr));
            assert(forall|vaddr: nat| s2.is_unmap_vaddr(vaddr) <==> s1.is_unmap_vaddr(vaddr));
            assert(s2.mmu@.pending_unmaps =~= s1.mmu@.pending_unmaps) by {
                assert forall|va|
                    s2.mmu@.pending_unmaps.contains_key(va)
                        implies
                    s1.mmu@.pending_unmaps.contains_key(va)
                by {
                    assert(!s2.mmu@.pt_mem@.contains_key(va));
                    assert(!s2.interp_pt_mem().contains_key(va as nat));
                };
            };
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
        },
        os::Step::UnmapEnd { core } => {
            let vaddr = s1.core_states[core].unmap_vaddr();
            assert forall|tlb_core: Core|
                #[trigger] c.valid_core(tlb_core)
                implies
                !s1.mmu@.tlbs[tlb_core].dom().contains(vaddr as usize)
            by {
                if s1.core_states[core] is UnmapOpDone {
                    let tlb_set = s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set());
                    assert(!tlb_set.contains(vaddr));
                    assert(s1.mmu@.tlbs[tlb_core].dom().map(|v| v as nat).subset_of(tlb_set));
                    assert(!s1.mmu@.tlbs[tlb_core].dom().map(|v| v as nat).contains(vaddr));
                    assert(vaddr <= usize::MAX);
                    assert(!s1.mmu@.tlbs[tlb_core].dom().contains(vaddr as usize));
                } else {
                    assert(!s1.os_ext.shootdown_vec.open_requests.contains(tlb_core));
                    assert(!s1.mmu@.tlbs[tlb_core].dom().contains(vaddr as usize));
                }
            }
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
        },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of overlapping virtual memory Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn next_step_preserves_overlap_mem_inv(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    step: os::Step,
    lbl: RLbl,
)
    requires
        s1.inv_basic(c),
        s1.inv_mmu(c),
        s1.overlapping_mem_inv(c),
        s2.inv_basic(c),
        s2.inv_mmu(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.overlapping_mem_inv(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    let _ = s2.interp_pt_mem(); let _ = s1.interp_pt_mem();

    if s2.sound {
        match step {
            // Map steps
            os::Step::MapStart { core } => {
                let thread_id = lbl->MapStart_thread_id;
                let vaddr = lbl->MapStart_vaddr;
                let pte = lbl->MapStart_pte;
                let corestate = os::CoreState::MapWaiting { ult_id: thread_id, vaddr, pte };
                lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert forall|core1: Core, core2: Core|
                        (c.valid_core(core1) && c.valid_core(core2)
                            && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                            && overlap(
                            MemRegion {
                                base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                                size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                            },
                            MemRegion {
                                base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                                size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                            },
                        )) implies core1 === core2
                by {
                    if (core1 == core || core2 == core) {
                        let other = if core1 != core { core1 } else { core2 };
                        assert(!os::candidate_mapping_overlaps_inflight_pmem(s1.interp_pt_mem(), s1.core_states.values(), pte));
                        if (other != core) {
                            assert(s2.core_states[other] == s1.core_states[other]);
                            assert(s1.core_states.dom().contains(other));
                            assert(s1.core_states.values().contains(s2.core_states[other]));
                            assert(os::candidate_mapping_overlaps_inflight_pmem(s1.interp_pt_mem(), s1.core_states.values(), pte));
                            assert(false);
                        }
                    }
                }
                assert(s2.inv_inflight_pmem_no_overlap_inflight_pmem(c));
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
                assert(s2.overlapping_mem_inv(c));
            },
            os::Step::MapOpStart { core } => {
                let vaddr = s1.core_states[core]->MapWaiting_vaddr;
                let pte = s1.core_states[core]->MapWaiting_pte;
                let ult_id = s1.core_states[core]->MapWaiting_ult_id;
                let corestate = os::CoreState::MapExecuting { ult_id, vaddr, pte };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
                assert (s2.inv_inflight_pmem_no_overlap_inflight_pmem(c)) by {
                    assert forall |core1: Core, core2: Core| #![auto]
                            (c.valid_core(core1) && c.valid_core(core2)
                                //might also need unmaps
                                && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                                && overlap(
                                MemRegion {
                                    base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                                    size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                                    size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                                },
                            )) implies core1 === core2 by {
                                assert(s1.core_states[core1].has_pte(s1.interp_pt_mem()) && s1.core_states[core2].has_pte(s1.interp_pt_mem()));
                                assert(s1.core_states[core1].pte_size(s1.interp_pt_mem()) == s2.core_states[core1].pte_size(s2.interp_pt_mem()));
                                assert(s1.core_states[core2].pte_size(s1.interp_pt_mem()) == s2.core_states[core2].pte_size(s2.interp_pt_mem()));
                                assert(overlap(
                                MemRegion {
                                    base: s1.core_states[core1].paddr(s1.interp_pt_mem()),
                                    size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s1.core_states[core2].paddr(s1.interp_pt_mem()),
                                    size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                                },));
                                assert( core1 === core2);
                            }
                }
                assert(s2.overlapping_mem_inv(c));
            },
            os::Step::MapNoOp { core }
            | os::Step::MapOpChange { core, .. } => {
                step_MapNoOp_and_step_MapOpChange_preserves_overlap_mem_inv(c, s1, s2, step, lbl);
            },
            //Unmap steps
            os::Step::UnmapStart { core } => {
                let ult_id = lbl->UnmapStart_thread_id;
                let vaddr = lbl->UnmapStart_vaddr;
                let corestate = os::CoreState::UnmapWaiting { ult_id, vaddr };
                let pte_size = if s1.interp_pt_mem().contains_key(vaddr) {
                    s1.interp_pt_mem()[vaddr].frame.size
                } else {
                    0
                };
                lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert forall|core1: Core, core2: Core|
                        (c.valid_core(core1) && c.valid_core(core2)
                            && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                            && overlap(
                            MemRegion {
                                base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                                size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                            },
                            MemRegion {
                                base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                                size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                            },
                        )) implies core1 === core2
                by {
                    if (core1 == core || core2 == core) {
                        let other = if core1 != core { core1 } else { core2 };
                        assert(!os::candidate_mapping_overlaps_inflight_vmem(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte_size));
                        assert(s2.core_states[core].has_pte(s2.interp_pt_mem()));
                        assert(s1.interp_pt_mem().contains_key(vaddr));
                        if (other != core) {
                            assert(s2.core_states[other] == s1.core_states[other]);
                            assert(s1.core_states.dom().contains(other));
                            assert(s1.core_states.values().contains(s2.core_states[other]));
                            assert(false);
                        }
                    }
                }
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
                assert(s2.overlapping_mem_inv(c));
            },
            os::Step::UnmapOpStart { core } => {
                let vaddr = s1.core_states[core]->UnmapWaiting_vaddr;
                let ult_id = s1.core_states[core]->UnmapWaiting_ult_id;
                let corestate = os::CoreState::UnmapExecuting { ult_id, vaddr, result: None };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
                assert (s2.inv_inflight_pmem_no_overlap_inflight_pmem(c)) by {
                    assert forall |core1: Core, core2: Core| #![auto]
                            (c.valid_core(core1) && c.valid_core(core2)
                                //might also need unmaps
                                && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                                && overlap(
                                MemRegion {
                                    base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                                    size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                                    size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                                },
                            )) implies core1 === core2 by {
                                assert(s1.core_states[core1].has_pte(s1.interp_pt_mem()) && s1.core_states[core2].has_pte(s1.interp_pt_mem()));
                                assert(s1.core_states[core1].pte_size(s1.interp_pt_mem()) == s2.core_states[core1].pte_size(s2.interp_pt_mem()));
                                assert(s1.core_states[core2].pte_size(s1.interp_pt_mem()) == s2.core_states[core2].pte_size(s2.interp_pt_mem()));
                                assert(overlap(
                                MemRegion {
                                    base: s1.core_states[core1].paddr(s1.interp_pt_mem()),
                                    size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s1.core_states[core2].paddr(s1.interp_pt_mem()),
                                    size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                                },));
                                assert( core1 === core2);
                            }
                }
                assert(s2.overlapping_mem_inv(c));
            },
            os::Step::UnmapOpChange { core, .. } => {
                let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;

                let pt = s1.interp_pt_mem();
                //proofgoal (1/2):  assert(s2.inv_inflight_map_no_overlap_inflight_vmem(c));
                assert( s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));
                assert( s1.core_states[core].pte_size(s1.interp_pt_mem()) >= s2.core_states[core].pte_size(s2.interp_pt_mem()));
                lemma_insert_preserves_no_overlap(c, s1.core_states, s1.interp_pt_mem(), core, s2.core_states[core]);
                assert forall|state1, state2|
                    s2.core_states.values().contains(state1) && s2.core_states.values().contains(state2)
                    && !state1.is_idle() && !state2.is_idle() && overlap(
                        MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
                        MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
                    ) implies state1 == state2
                by {
                    if (state1 === s2.core_states[core] || state2 == s2.core_states[core]) {
                        let other_state = if state1 === s2.core_states[core] {state2} else {state1};
                    }
                }
                lemma_submap_preserves_no_overlap(c, s2.core_states, s1.interp_pt_mem(), s2.interp_pt_mem());
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));
                assert forall|base| #[trigger] s2.interp_pt_mem().dom().contains(base) implies
                    !candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base])
                by {
                    assert(s2.interp_pt_mem().dom().contains(base));
                    if candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base],
                    ) {
                        let overlap_vaddr = choose|b: nat| #![auto] {
                            &&& s2.interp_pt_mem().remove(base).dom().contains(b)
                            &&& overlap(
                                MemRegion {
                                    base: base,
                                    size: s2.interp_pt_mem()[base].frame.size,
                                },
                                MemRegion { base: b, size: s2.interp_pt_mem()[b].frame.size },
                            )
                        };
                        assert(s1.interp_pt_mem().remove(base).dom().contains(overlap_vaddr));
                        // assert(s1.inv_existing_map_no_overlap_existing_vmem(c));
                        assert(false);
                    }
                }
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
                assert (s2.inv_inflight_pmem_no_overlap_inflight_pmem(c)) by {
                        assert forall |core1: Core, core2: Core|
                                (c.valid_core(core1) && c.valid_core(core2)
                                    && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                                    && overlap(
                                    MemRegion {
                                        base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                                        size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                                    },
                                    MemRegion {
                                        base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                                        size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                                    },
                                )) implies core1 === core2 by {
                                    assert (s1.core_states[core1].has_pte(s1.interp_pt_mem()) && s1.core_states[core2].has_pte(s1.interp_pt_mem()));
                                    assert (s1.core_states[core1].pte_size(s1.interp_pt_mem()) == s2.core_states[core1].pte_size(s2.interp_pt_mem()));
                                    assert (s1.core_states[core2].pte_size(s1.interp_pt_mem()) == s2.core_states[core2].pte_size(s2.interp_pt_mem()));
                                    assert(overlap( MemRegion {
                                        base: s1.core_states[core1].paddr(s1.interp_pt_mem()),
                                        size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                                    },
                                    MemRegion {
                                        base: s1.core_states[core2].paddr(s1.interp_pt_mem()),
                                        size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                                    },));
                                }
                }
                assert(s2.overlapping_mem_inv(c));
            },
            os::Step::UnmapOpFail { core } => {
                let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;
                let corestate = os::CoreState::UnmapOpDone { ult_id, vaddr, result: Err(()) };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.inv_inflight_pmem_no_overlap_inflight_pmem(c));
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapInitiateShootdown { core } => {
                let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;
                let result = s1.core_states[core]->UnmapExecuting_result;
                let corestate = os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result: result->Some_0 };
                lemma_insert_preserves_no_overlap(c, s1.core_states, s1.interp_pt_mem(), core, corestate);
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert (s2.inv_inflight_pmem_no_overlap_inflight_pmem(c)) by {
                    assert forall |core1: Core, core2: Core|
                            (c.valid_core(core1) && c.valid_core(core2)
                                && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                                && overlap(
                                MemRegion {
                                    base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                                    size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                                    size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                                },
                            )) implies core1 === core2 by {
                                assert(s1.core_states[core1].has_pte(s1.interp_pt_mem()) && s1.core_states[core2].has_pte(s2.interp_pt_mem()));
                                assert (s1.core_states[core1].pte_size(s1.interp_pt_mem()) == s2.core_states[core1].pte_size(s2.interp_pt_mem()));
                                assert (s1.core_states[core2].pte_size(s1.interp_pt_mem()) == s2.core_states[core2].pte_size(s2.interp_pt_mem()));
                                assert(overlap( MemRegion {
                                    base: s1.core_states[core1].paddr(s1.interp_pt_mem()),
                                    size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s1.core_states[core2].paddr(s1.interp_pt_mem()),
                                    size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                                },));
                            }
                }
                assert(s2.inv_existing_map_no_overlap_existing_vmem(c));
                assert(s2.overlapping_mem_inv(c));
            },
            _ => { assert(s2.overlapping_mem_inv(c));
            },
        }
    }
}

pub proof fn step_MapNoOp_and_step_MapOpChange_preserves_overlap_mem_inv(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    step: os::Step,
    lbl: RLbl,
)
    requires
        s1.inv_basic(c),
        s1.inv_mmu(c),
        s1.overlapping_mem_inv(c),
        s2.inv_basic(c),
        s2.inv_mmu(c),
        s2.sound,
        os::next_step(c, s1, s2, step, lbl),
        step is MapOpChange || step is MapNoOp
    ensures
        s2.overlapping_mem_inv(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    let _ = s2.interp_pt_mem(); let _ = s1.interp_pt_mem();
    let core = match step {
        os::Step::MapNoOp { core }
        | os::Step::MapOpChange { core, .. } => core,
        _ => arbitrary()
    };


    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
    let ult_id = s1.core_states[core]->MapExecuting_ult_id;
    let pte = s1.core_states[core]->MapExecuting_pte;
    let result = if (step is MapOpChange) { Ok(()) } else { Err(()) };
    let corestate = os::CoreState::MapDone { ult_id, vaddr, pte, result};
    assert(unique_CoreStates(s2.core_states));
    assert(no_overlap_vmem_values(s2.core_states, s2.interp_pt_mem())) by {
        assert forall|state1: os::CoreState, state2: os::CoreState|
            s2.core_states.values().contains(state1) && s2.core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
                MemRegion {
                    base: state1.vaddr(),
                    size: state1.pte_size(s2.interp_pt_mem()),
                },
                MemRegion {
                    base: state2.vaddr(),
                    size: state2.pte_size(s2.interp_pt_mem()),
                },
            ) implies state1 == state2
        by {
            if state1.vaddr() == vaddr || state2.vaddr() == vaddr {
                let other = if state1 != corestate { state1 } else { state2 };
                if other != corestate {
                    assert(overlap(
                        MemRegion { base: other.vaddr(), size: other.pte_size(s1.interp_pt_mem()) },
                        MemRegion {
                            base: s1.core_states[core].vaddr(),
                            size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                        },
                    ));
                    let other_core = choose|b|
                        #![auto]
                        s1.core_states.insert(core, corestate).dom().contains(b) && s1.core_states[b] == other
                            && b != core;
                    assert(s1.core_states.remove(core).dom().contains(other_core));
                    assert(false);
                }
            } else {
                if s1.interp_pt_mem().dom().contains(state1.vaddr()) {
                    assert(overlap(
                        MemRegion {
                            base: state1.vaddr(),
                            size: state1.pte_size(s1.interp_pt_mem()),
                        },
                        MemRegion {
                            base: state2.vaddr(),
                            size: state2.pte_size(s1.interp_pt_mem()),
                        },
                    ));
                } else {
                    assert(!s2.interp_pt_mem().dom().contains(state1.vaddr()));
                }
            }
        };
    };

    lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
    assert(s2.inv_inflight_map_no_overlap_inflight_vmem(c));


    assert(s2.inv_existing_map_no_overlap_existing_vmem(c)) by {
        assert forall|x, y| #![auto] (s2.interp_pt_mem().contains_key(x) && s2.interp_pt_mem().remove(x).dom().contains(y))
        implies ( !overlap(
            MemRegion { base: x, size: s2.interp_pt_mem()[x].frame.size },
            MemRegion { base: y, size:  s2.interp_pt_mem().remove(x)[y].frame.size })) by
        {
            if x != vaddr && y != vaddr {
                assert(x != y);
                assert(s1.interp_pt_mem().dom().contains(x));
                assert(s1.interp_pt_mem().dom().contains(y));
                assert(!s1.interp_pt_mem().remove(x).dom().contains(y) || !overlap(
                    MemRegion { base: x, size: s1.interp_pt_mem()[x].frame.size },
                    MemRegion { base: y, size:  s1.interp_pt_mem().remove(x)[y].frame.size }));
            }
        }
    };
    assert(s2.inv_inflight_pmem_no_overlap_inflight_pmem(c)) by {
        assert forall |core1: Core, core2: Core| #![auto]
                (c.valid_core(core1) && c.valid_core(core2)
                    && s2.core_states[core1].has_pte(s2.interp_pt_mem()) && s2.core_states[core2].has_pte(s2.interp_pt_mem())
                    && overlap(
                    MemRegion {
                        base: s2.core_states[core1].paddr(s2.interp_pt_mem()),
                        size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s2.core_states[core2].paddr(s2.interp_pt_mem()),
                        size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                    },
                )) implies core1 === core2 by {
                    if (s1.core_states[core1].has_pte(s1.interp_pt_mem())
                        && s1.core_states[core2].has_pte(s1.interp_pt_mem())
                        && s1.core_states[core1].pte_size(s1.interp_pt_mem()) == s2.core_states[core1].pte_size(s2.interp_pt_mem())
                        && s1.core_states[core2].pte_size(s1.interp_pt_mem()) == s2.core_states[core2].pte_size(s2.interp_pt_mem()))
                    {
                    assert(overlap(
                    MemRegion {
                        base: s1.core_states[core1].paddr(s1.interp_pt_mem()),
                        size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[core2].paddr(s1.interp_pt_mem()),
                        size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                    },));
                    assert( core1 === core2);
                    } else {
                    //this is the case where an unmap started and the entry is mapped now
                        let unmap_core = if !s1.core_states[core1].has_pte(s1.interp_pt_mem()) || !(s1.core_states[core1].pte_size(s1.interp_pt_mem()) == s2.core_states[core1].pte_size(s2.interp_pt_mem())) {
                            core1
                        } else {
                            core2
                        };
                    assert(s1.core_states[unmap_core] is UnmapWaiting);
                    assert(s1.core_states[unmap_core]->UnmapWaiting_vaddr == vaddr);
                    assert (c.valid_core(core) && c.valid_core(unmap_core)
                    && !s1.core_states[core].is_idle() && !s1.core_states[unmap_core].is_idle());
                    assert(overlap(
                        MemRegion {
                            base: s1.core_states[core].vaddr(),
                            size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s1.core_states[unmap_core].vaddr(),
                            size: s1.core_states[unmap_core].pte_size(s1.interp_pt_mem()),
                        },));
                    assert(!s1.inv_inflight_map_no_overlap_inflight_vmem(c));
                    }
                }
    }

    assert(s2.inv_inflight_pmem_no_overlap_existing_pmem(c)) by {
        assert forall|map_core| #![auto](c.valid_core(map_core) && s2.core_states[map_core].is_map()) && !(s2.core_states[map_core] is MapDone)
        implies !mmu::defs::candidate_mapping_overlaps_existing_pmem(
                s2.interp_pt_mem(),
                s2.core_states[map_core].PTE()
        ) by {
            if map_core != core && mmu::defs::candidate_mapping_overlaps_existing_pmem(
                s2.interp_pt_mem(),
                s2.core_states[map_core].PTE())
            {
                assert(c.valid_core(map_core) && c.valid_core(core));
                // i changed smth here
                assert(s1.core_states[map_core].has_pte(s1.interp_pt_mem()) && s1.core_states[core].has_pte(s1.interp_pt_mem()));
                assert(overlap(
                    MemRegion {
                        base: s1.core_states[core].paddr(s1.interp_pt_mem()),
                        size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[map_core].paddr(s1.interp_pt_mem()),
                        size: s1.core_states[map_core].pte_size(s1.interp_pt_mem()),
                    },
                ));
                assert(!s1.inv_inflight_pmem_no_overlap_inflight_pmem(c));
                assert(false);
            }
        }
    };
    assert(s2.inv_mapped_pmem_no_overlap(c));
    assert(s2.overlapping_mem_inv(c));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Alternative Definition for inv_inflight_map_no_overlap_inflight_vmem and Equivalence proof
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn unique_CoreStates(map: Map<Core, os::CoreState>) -> bool {
    forall|core| #![auto] map.contains_key(core) && !map[core].is_idle()
        ==> !map.remove(core).values().contains(map[core])
}

pub open spec fn no_overlap_vmem_values(
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
) -> bool {
    forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
        ) ==> state1 == state2
}

//pub proof fn lemma_overlapping_inv_implies_unique_and_overlap_values(
//    c: os::Constants,
//    s: os::State,
//)
//    requires
//        s.inv_basic(c),
//        s.inv_inflight_map_no_overlap_inflight_vmem(c),
//    ensures
//        unique_CoreStates(s.core_states),
//        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
//{
//}

pub proof fn lemma_unique_and_overlap_values_implies_overlap_vmem(
    c: os::Constants,
    s: os::State,
)
    requires
        unique_CoreStates(s.core_states),
        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
        s.inv_basic(c),
    ensures
        s.inv_inflight_map_no_overlap_inflight_vmem(c),
{
    assert(forall|core| #[trigger] c.valid_core(core) ==> s.core_states.contains_key(core));
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata to help proof inv_inflight_map_no_overlap_inflight_vmem
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//pub proof fn lemma_insert_idle_corestate_preserves_no_overlap(
//    c: os::Constants,
//    core_states: Map<Core, os::CoreState>,
//    pt: Map<nat, PTE>,
//    core: Core,
//)
//    requires
//        core_states.dom().contains(core),
//        unique_CoreStates(core_states),
//        no_overlap_vmem_values(core_states, pt),
//    ensures
//        unique_CoreStates(core_states.insert(core, os::CoreState::Idle)),
//        no_overlap_vmem_values(core_states.insert(core, os::CoreState::Idle), pt),
//{
//    assert forall|a|
//        #![auto]
//        core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
//            core,
//            os::CoreState::Idle,
//        ).index(a).is_idle() implies !core_states.insert(core, os::CoreState::Idle).remove(
//        a,
//    ).values().contains(core_states.insert(core, os::CoreState::Idle).index(a)) by {
//        if core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
//            core,
//            os::CoreState::Idle,
//        ).index(a).is_idle() && a != core {
//            assert(core_states.dom().contains(a));
//            assert(core_states.index(a) == core_states.insert(core, os::CoreState::Idle).index(a));
//            assert(!core_states.index(a).is_idle());
//            assert(!core_states.remove(a).values().contains(core_states.index(a)));
//
//            assert(core_states.insert(core, os::CoreState::Idle).remove(a) =~= core_states.remove(
//                a,
//            ).insert(core, os::CoreState::Idle));
//
//            lemma_map_insert_values_equality(core_states.remove(a), core, os::CoreState::Idle);
//        }
//    };
//    assert(no_overlap_vmem_values(core_states.insert(core, os::CoreState::Idle), pt));
//}

pub proof fn lemma_insert_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    new_cs: os::CoreState,
)
    requires
        new_cs.is_in_crit_sect(),
        forall|cr| #![auto] core_states.dom().contains(cr) && core_states[cr].is_in_crit_sect() ==> cr == core,
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        !core_states[core].is_idle(),
        !new_cs.is_idle(),
        core_states[core].vaddr() == new_cs.vaddr(),
        core_states[core].pte_size(pt) >= new_cs.pte_size(pt),
        core_states[core] != new_cs,
    ensures
        unique_CoreStates(core_states.insert(core, new_cs)),
        no_overlap_vmem_values(core_states.insert(core, new_cs), pt),
{
    assert forall|a| #![auto]
        core_states.insert(core, new_cs).dom().contains(a) && !core_states.insert(core, new_cs)[a].is_idle()
        implies !core_states.insert(core, new_cs).remove(a).values().contains(core_states.insert(core, new_cs).index(a))
    by {
        if a != core {
            assert(!core_states[a].is_in_crit_sect());
            if core_states.insert(core, new_cs).remove(a).values().contains(core_states.insert(core, new_cs)[a]) {
                let same_core = choose|cr| #![auto]
                    core_states.insert(core, new_cs).dom().contains(cr) && core_states.insert(
                        core,
                        new_cs,
                    )[cr] == core_states.insert(core, new_cs)[a] && cr != a;
                assert(core_states.remove(a).dom().contains(same_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, new_cs).values().contains(state1) && core_states.insert(
            core,
            new_cs,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
        ) implies state1 == state2 by {
        if state1 == new_cs || state2 == new_cs {
            let other = if state1 != new_cs { state1 } else { state2 };
            if other != new_cs {
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.pte_size(pt) },
                    MemRegion {
                        base: core_states[core].vaddr(),
                        size: core_states[core].pte_size(pt),
                    },
                ));
                let other_core = choose|b|
                    #![auto]
                    core_states.insert(core, new_cs).dom().contains(b) && core_states[b] == other
                        && b != core;
                assert(core_states.remove(core).dom().contains(other_core));
                assert(false);
            }
        }
    }
}

pub proof fn lemma_insert_no_overlap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    corestate: os::CoreState,
)
    requires
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        core_states[core].is_idle(),
        !corestate.is_idle(),
        !os::candidate_mapping_overlaps_inflight_vmem(
            pt,
            core_states.values(),
            corestate.vaddr(),
            corestate.pte_size(pt),
        ),
    ensures
        unique_CoreStates(core_states.insert(core, corestate)),
        no_overlap_vmem_values(core_states.insert(core, corestate), pt),
{
    assert forall|a| #![auto]
        core_states.insert(core, corestate).dom().contains(a)
        && !core_states.insert(core, corestate)[a].is_idle()
        implies !core_states.insert(core, corestate).remove(a).values()
                            .contains(core_states.insert(core, corestate)[a])
    by {
        if core_states.insert(core, corestate).remove(a).values().contains(
            core_states.insert(core, corestate)[a],
        ) {
            let some_core = choose|cr|
                #![auto]
                cr != a && core_states.insert(core, corestate).dom().contains(cr)
                    && core_states.insert(core, corestate)[cr] == core_states.insert(
                    core,
                    corestate,
                )[a];
            if a == core || some_core == core {
                let other = if some_core != core { some_core } else { a };
                assert(core_states.values().contains(core_states[other]));
                assert(overlap(
                    MemRegion {
                        base: core_states[other].vaddr(),
                        size: core_states[other].pte_size(pt),
                    },
                    MemRegion { base: corestate.vaddr(), size: corestate.pte_size(pt) },
                ));
            } else {
                assert(core_states.remove(a).dom().contains(some_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, corestate).values().contains(state1) && core_states.insert(
            core,
            corestate,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
        ) implies state1 == state2 by {
        if state1 == corestate || state2 == corestate {
            let other = if state1 != corestate {
                state1
            } else {
                state2
            };
            if other != corestate {
                assert(core_states.values().contains(other));
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.pte_size(pt) },
                    MemRegion { base: corestate.vaddr(), size: corestate.pte_size(pt) },
                ));
                assert(false);
            }
        }
    }
}

pub proof fn lemma_submap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    sub_pt: Map<nat, PTE>,
)
    requires
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        sub_pt.submap_of(pt),
    ensures
        no_overlap_vmem_values(core_states, sub_pt),
{
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(sub_pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(sub_pt) },
        ) implies state1 == state2 by {
        assert(overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
        ));
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(
    c: os::Constants,
    s: os::State,
    base: nat,
    candidate_size: nat,
)
    requires
        s.inv_basic(c),
    ensures
        os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate_size,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate_size,
    )) by {
        if os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ) {
            let corestate = choose|b: os::CoreState| #![auto]
                {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. }
                        | os::CoreState::MapDone { vaddr, pte, .. } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        os::CoreState::UnmapWaiting { vaddr, .. }
                        | os::CoreState::UnmapExecuting { vaddr, result: None, .. } => {
                            let size = if s.interp_pt_mem().dom().contains(vaddr) {
                                s.interp_pt_mem().index(vaddr).frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        os::CoreState::UnmapExecuting { vaddr, result: Some(result), .. }
                        | os::CoreState::UnmapOpDone { vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                            let size = if result is Ok {
                                result.get_Ok_0().frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        _ => { false },
                    }
                };
            let core = choose|core| #[trigger] c.valid_core(core) && s.core_states[core] == corestate;
            match corestate {
                os::CoreState::MapWaiting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapDone { ult_id, vaddr, pte, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state[ult_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                },
                os::CoreState::UnmapWaiting { ult_id, vaddr }
                | os::CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                },
                os::CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                    //assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.contains_key(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    //if result is Ok {}
                },
                _ => {},
            };
        }
    };
}

pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(
    c: os::Constants,
    s: os::State,
    base: nat,
    candidate_size: nat,
)
    requires
        s.inv_basic(c),
    ensures
        hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ) ==> os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate_size,
    ) ==> os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate_size,
    )) by {
        if hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ) {
            let thread_state = choose|b|
                {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::ThreadState::Map { vaddr, pte } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        hlspec::ThreadState::Unmap { vaddr, pte } => {
                            let size = if pte.is_some() {
                                pte.unwrap().frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        _ => { false },
                    }
                };
            let ult_id = choose|id| #[trigger] c.valid_ult(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ult(ult_id));
            let core = c.ult2core[ult_id];
            assert(c.valid_core(core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte, .. } => {
                    assert(ult_id2 == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    ));
                },
                os::CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                | os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: None, .. } => {
                    assert(ult_id2 == ult_id);
                    if s.interp_pt_mem().dom().contains(vaddr) {
                        let pte = s.interp_pt_mem()[vaddr];
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: Some(entry),
                            }
                            &&& vaddr === v_addr
                            &&& entry === pte
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    } else {
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: None,
                            }
                            &&& vaddr === v_addr
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: 0 },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    }
                },
                os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result, .. } => {
                    if result is Ok {
                        assert(ult_id2 == ult_id);
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: Some(pte),
                            }
                            &&& vaddr === v_addr
                            &&& result.get_Ok_0() === pte
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: result.get_Ok_0().frame.size },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    } else {
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: None,
                            }
                            &&& vaddr === v_addr
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: 0 },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    }
                },
                _ => {},
            };
        }
    };

}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(
    c: os::Constants,
    s: os::State,
    candidate: PTE,
)
    requires
        s.inv_basic(c),
        candidate.frame.size > 0,
    ensures
        os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_pmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        candidate,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    )) by {
        if os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ) {
            let corestate = choose|b: os::CoreState| #![auto] {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. }
                        | os::CoreState::MapDone { vaddr, pte, .. } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                            &&& s.interp_pt_mem().dom().contains(vaddr)
                            &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                        },
                        os::CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                            &&& result is Ok
                            &&& overlap(candidate.frame, result.get_Ok_0().frame)
                        },
                        os::CoreState::Idle => false,
                    }
                };
            let core = choose|core| #[trigger] s.core_states.dom().contains(core) && s.core_states[core] == corestate;
            assert(c.valid_core(core));
            match corestate {
                os::CoreState::MapWaiting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapDone { ult_id, vaddr, pte, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state[ult_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_address,
                            pte: p_te,
                        }
                        &&& v_address === vaddr
                        &&& p_te === pte
                        &&& overlap(candidate.frame, pte.frame)
                    });
                },
                os::CoreState::UnmapWaiting { ult_id, vaddr }
                | os::CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_address,
                            pte: Some(pte),
                        }
                        &&& v_address === vaddr
                        &&& s.interp_pt_mem()[vaddr] === pte
                        &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                    });
                },
                os::CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_address,
                            pte: pte,
                        }
                        &&& v_address === vaddr
                        &&& match result {
                            Ok(pte_) => pte is Some && pte_ == pte->0,
                            Err(_) => pte is None,
                        }
                        &&& overlap(candidate.frame, pte->0.frame)
                    });
                },
                _ => {},
            };
        }
    };
}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(
    c: os::Constants,
    s: os::State,
    candidate: PTE,
)
    requires
        s.inv_basic(c),
        candidate.frame.size > 0,
    ensures
        hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ) ==> os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    ) ==> os::candidate_mapping_overlaps_inflight_pmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        candidate,
    )) by {
        if hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ) {
            let thread_state = choose|b| {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::ThreadState::Map { vaddr, pte } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        hlspec::ThreadState::Unmap { vaddr, pte } => {
                            &&& pte.is_some()
                            &&& overlap(candidate.frame, pte.unwrap().frame)
                        },
                        _ => { false },
                    }
                };
            let ult_id = choose|id| #[trigger]
                c.valid_ult(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ult(ult_id));
            let core = c.ult2core[ult_id];
            assert(c.valid_core(core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte, .. } => {
                    assert(ult_id == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, pte.frame));
                },
                os::CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                | os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: None, .. } => {
                    assert(s.interp_pt_mem().dom().contains(vaddr));
                    assert(ult_id == ult_id);
                    let pte = s.interp_pt_mem()[vaddr];
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_addr,
                            pte: Some(entry),
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame));
                },
                os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result, .. } => {
                    assert(ult_id == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_addr,
                            pte,
                        }
                        &&& vaddr === v_addr
                        &&& match result {
                            Ok(pte_) => pte is Some && pte_ == pte->0,
                            Err(_) => pte is None,
                        }
                    });
                    assert(overlap(candidate.frame, result.get_Ok_0().frame));
                },
                _ => {},
            };
        }
    };
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// usefull lemmata about maps
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub proof fn lemma_map_insert_values_equality<A, B>(map: Map<A, B>, key: A, value: B)
    requires
        map.dom().contains(key),
    ensures
        map.values().insert(value) === map.insert(key, value).values().insert(map.index(key)),
{
    assert forall|values| #![auto] map.values().insert(value).contains(values)
        implies map.insert(key, value).values().insert(map.index(key)).contains(values)
    by {
        if values == value {
            lemma_map_insert_value(map, key, value);
        } else {
            let k = choose|some_key| #[trigger]
                map.dom().contains(some_key) && (map[some_key] == values);
            assert(map.insert(key, value).dom().contains(k));
            if k == key {
                assert(map.index(key) == values);
            } else {
                assert(map[k] === map.insert(key, value)[k]);
            }
        }
    }
    assert(map.values().insert(value) =~= map.insert(key, value).values().insert(map.index(key)));
}

pub proof fn lemma_map_insert_value<A, B>(map: Map<A, B>, key: A, value: B)
    requires
    ensures
        map.insert(key, value).values().contains(value),
{
    assert(map.insert(key, value).dom().contains(key));
    assert(map.insert(key, value)[key] == value);
}

} // verus!
