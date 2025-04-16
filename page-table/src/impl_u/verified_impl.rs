use vstd::prelude::*;

use crate::theorem::RLbl;
use crate::spec_t::mmu::defs::{ PageTableEntryExec, MemRegionExec };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ candidate_mapping_overlaps_existing_vmem, MAX_BASE, x86_arch_spec, x86_arch_spec_upper_bound };
use crate::spec_t::os_ext;
use crate::spec_t::mmu;
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::os_code_vc::{ Token, CodeVC, HandlerVC, lemma_concurrent_trs_during_shootdown };
use crate::impl_u::wrapped_token::{ self, WrappedMapToken, WrappedUnmapToken, WrappedTokenView, DoShootdown };
use crate::impl_u::l2_impl::PT::{ self, map_frame, unmap };
use crate::spec_t::os;

verus! {

pub struct PTImpl {}

impl CodeVC for PTImpl {
    exec fn sys_do_map(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        pte: PageTableEntryExec,
    ) -> (Result<(),()>, Tracked<Token>)
    {
        let tracked mut tok = tok;

        wrapped_token::start_map_and_acquire_lock(Tracked(&mut tok), Ghost(vaddr as nat), Ghost(pte@));
        let tracked wtok = WrappedMapToken::new(tok); //, tok.steps()[0]->MapEnd_result);
        proof {
            wtok.lemma_regions_derived_from_view();
        }
        let mut pt = Ghost(choose|pt| PT::inv_and_nonempty(wtok@, pt));
        assert(PT::inv_and_nonempty(wtok@, pt@));

        proof {
            x86_arch_spec_upper_bound();
            assert(vaddr < MAX_BASE);
            assert(x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size as nat, 1)) by {
                assert(x86_arch_spec.entry_size(1) == crate::spec_t::mmu::defs::L1_ENTRY_SIZE);
                assert(x86_arch_spec.entry_size(2) == crate::spec_t::mmu::defs::L2_ENTRY_SIZE);
                assert(x86_arch_spec.entry_size(3) == crate::spec_t::mmu::defs::L3_ENTRY_SIZE);
            };
        }

        let ghost wtok_before = wtok@;
        let ghost pt_before = pt@;

        let res = map_frame(Tracked(&mut wtok), &mut pt, pml4, vaddr, pte);
        assert(PT::inv_and_nonempty(wtok@, pt@));
        assert forall|wtokp: WrappedTokenView| ({
            &&& wtokp.pt_mem == wtok@.pt_mem
            &&& wtokp.regions.dom() == wtok@.regions.dom()
            &&& #[trigger] wtokp.regions_derived_from_view()
        }) implies exists|pt| PT::inv_and_nonempty(wtokp, pt) by {
            wtok.lemma_regions_derived_from_view();
            PT::lemma_inv_at_changed_tok(wtok@, wtokp, pt@, 0, pt@.region.base as usize);
            PT::lemma_no_empty_directories_with_changed_tok(wtok@, pt@, wtokp, pt@, 0, pt@.region.base as usize, 0);
            assert(PT::inv_and_nonempty(wtokp, pt@));
        };

        if let Err(_) = res {
            proof {
                assert(candidate_mapping_overlaps_existing_vmem(
                    PT::interp_to_l0(wtok@, pt@),
                    wtok@.args->Map_base as nat,
                    wtok@.args->Map_pte
                ));
                WrappedMapToken::register_failed_map(&mut wtok, pt@);
                assert(wtok@.result is Err);
            }
        }
        assert(wtok@.change_made);

        assert(res == wtok@.result) by {
            match res {
                Ok(v) => assert(v == ()),
                Err(v) => assert(v == ()),
            }
        };
        let tok = WrappedMapToken::finish_map_and_release_lock(Tracked(wtok));

        (res, tok)
    }

    exec fn sys_do_unmap(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
    ) -> (res: (Result<MemRegionExec,()>, Tracked<Token>))
    {
        let tracked mut tok = tok;

        wrapped_token::start_unmap_and_acquire_lock(Tracked(&mut tok), Ghost(vaddr as nat));
        let tracked wtok = WrappedUnmapToken::new(tok); //, tok.steps()[0]->MapEnd_result);
        proof {
            wtok.lemma_regions_derived_from_view();
        }
        let mut pt = Ghost(choose|pt| PT::inv_and_nonempty(wtok@, pt));
        assert(PT::inv_and_nonempty(wtok@, pt@));

        proof {
            x86_arch_spec_upper_bound();
            assert(vaddr < MAX_BASE);
            assert(x86_arch_spec.entry_size(1) == crate::spec_t::mmu::defs::L1_ENTRY_SIZE);
            assert(x86_arch_spec.entry_size(2) == crate::spec_t::mmu::defs::L2_ENTRY_SIZE);
            assert(x86_arch_spec.entry_size(3) == crate::spec_t::mmu::defs::L3_ENTRY_SIZE);
        }

        let ghost wtok_before = wtok@;
        let ghost pt_before = pt@;

        let res = unmap(Tracked(&mut wtok), &mut pt, pml4, vaddr);
        assert(PT::inv_and_nonempty(wtok@, pt@));
        assert forall|wtokp: WrappedTokenView| ({
            &&& wtokp.pt_mem == wtok@.pt_mem
            &&& wtokp.regions.dom() == wtok@.regions.dom()
            &&& #[trigger] wtokp.regions_derived_from_view()
        }) implies exists|pt| PT::inv_and_nonempty(wtokp, pt) by {
            wtok.lemma_regions_derived_from_view();
            PT::lemma_inv_at_changed_tok(wtok@, wtokp, pt@, 0, pt@.region.base as usize);
            PT::lemma_no_empty_directories_with_changed_tok(wtok@, pt@, wtokp, pt@, 0, pt@.region.base as usize, 0);
            assert(PT::inv_and_nonempty(wtokp, pt@));
        };

        let shootdown = if let Ok(pte) = res {
            DoShootdown::Yes { vaddr, size: pte.size }
        } else {
            DoShootdown::No
        };

        let tok = WrappedUnmapToken::finish_unmap_and_release_lock(Tracked(wtok), shootdown, pt);

        (res, tok)
    }
}

impl HandlerVC for PTImpl {
    exec fn handle_shootdown_ipi(Tracked(tok): Tracked<Token>, vaddr: usize) -> (res: Tracked<Token>) {
        let tracked mut tok = tok;
        let ghost core = tok.core();
        let ghost state1 = tok.st();

        proof {
            broadcast use to_rl1::next_refines;
            let pidx = tok.do_concurrent_trs();
            lemma_concurrent_trs_during_shootdown(state1, tok.st(), tok.consts(), tok.core(), pidx);
        }

        let ghost state2 = tok.st();

        let tracked mut mmu_tok = tok.get_mmu_token();
        proof {
            mmu_tok.prophesy_invlpg(vaddr);
            let post = os::State {
                mmu: mmu_tok.post(),
                ..tok.st()
            };
            assert(mmu::rl3::next(tok.st().mmu, post.mmu, tok.consts().common, mmu_tok.lbl()));
            assert(tok.st().os_ext.shootdown_vec.open_requests.contains(core));
            assert(os::step_Invlpg(tok.consts(), tok.st(), post, core, RLbl::Tau));
            let step = os::Step::Invlpg { core };
            assert(os::next_step(tok.consts(), tok.st(), post, step, RLbl::Tau));
            tok.register_internal_step_mmu(&mut mmu_tok, post, step);
            crate::spec_t::os_invariant::next_preserves_inv(tok.consts(), state2, tok.st(), RLbl::Tau);
        }
        // Execute invlpg to evict from local TLB
        mmu::rl3::code::invlpg(Tracked(&mut mmu_tok), vaddr);
        let ghost state3 = tok.st();

        proof {
            broadcast use to_rl1::next_refines;
            tok.return_mmu_token(mmu_tok);
            let pidx = tok.do_concurrent_trs();
            lemma_concurrent_trs_during_shootdown(state3, tok.st(), tok.consts(), tok.core(), pidx);
        }
        let ghost state4 = tok.st();

        let tracked mut osext_tok = tok.get_osext_token();
        proof {
            osext_tok.prophesy_ack_shootdown();
            let post = os::State {
                os_ext: osext_tok.post(),
                ..tok.st()
            };
            assert(os_ext::next(tok.st().os_ext, post.os_ext, tok.consts().common, osext_tok.lbl()));
            assert(state2.core_states[state2.os_ext.lock->Some_0] is UnmapShootdownWaiting);
            assert((state2.os_ext.lock matches Some(core) &&
                state2.core_states[core] matches os::CoreState::UnmapShootdownWaiting { .. }));
            assert(state2.mmu@.writes.tso === set![]);
            assert(state3.mmu@.writes.nonpos === state2.mmu@.writes.nonpos.remove(core));
            assert(!state3.mmu@.writes.nonpos.contains(core));
            assert(!tok.st().mmu@.writes.nonpos.contains(core));
            assert(!state3.mmu@.tlbs[core].contains_key(vaddr));
            assert(tok.consts().valid_core(state2.os_ext.lock->Some_0));
            assert(tok.consts().valid_core(core) );
            assert(tok.st().core_states[state2.os_ext.lock->Some_0] is UnmapShootdownWaiting);
            assert(!tok.st().mmu@.tlbs[core].contains_key(vaddr));
            let lbl = RLbl::AckShootdownIPI { core };
            assert(os::step_AckShootdownIPI(tok.consts(), tok.st(), post, core, lbl));
            let step = os::Step::AckShootdownIPI { core };
            assert(os::next_step(tok.consts(), tok.st(), post, step, lbl));
            tok.register_external_step_osext(&mut osext_tok, post, step, lbl);
            crate::spec_t::os_invariant::next_preserves_inv(tok.consts(), state4, tok.st(), lbl);
        }

        os_ext::code::ack_shootdown(Tracked(&mut osext_tok));
        let ghost state5 = tok.st();

        proof {
            broadcast use to_rl1::next_refines;
            tok.return_osext_token(osext_tok);
            assert(tok.steps() === seq![]);
        }

        Tracked(tok)
    }
}



} // verus!
