use vstd::prelude::*;

use crate::spec_t::os;
use crate::spec_t::os_invariant;
use crate::spec_t::mmu;
use crate::spec_t::os_ext;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ aligned, new_seq, bit, usize_keys, candidate_mapping_overlaps_existing_vmem_usize };
use crate::spec_t::mmu::defs::{ MemRegionExec, MemRegion, PTE, MAX_PHYADDR };
use crate::spec_t::mmu::translation::{ MASK_NEG_DIRTY_ACCESS };
use crate::theorem::RLbl;
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::os_code_vc::Token;
#[cfg(verus_keep_ghost)]
use crate::spec_t::os_code_vc::{ lemma_concurrent_trs, unchanged_state_during_concurrent_trs };
use crate::impl_u::l2_impl::{ PT, PTDir };

verus! {

/// We define a view of the wrapped map token with the memory stuff that the implementation uses to
/// define its invariant and interpretation. This way read-only ops (e.g. `read`) leave the view
/// fully unchanged, which simplifies reasoning. Otherwise we have to argue that the invariant is
/// preserved as only irrelevant parts of the state may have changed. (Since `read` still has to
/// take a mut ref as it changes the underlying token.)
pub struct WrappedMapTokenView {
    pub orig_st: os::State,
    pub args: (usize, PTE),
    pub regions: Map<MemRegion, Seq<usize>>,
    /// We also keep the flat memory directly because this is what the MMU's interpretation is
    /// defined on.
    pub pt_mem: mmu::pt_mem::PTMem,
}

impl WrappedMapTokenView {
    pub open spec fn read(self, idx: usize, r: MemRegion) -> usize {
        self.regions[r][idx as int] & MASK_NEG_DIRTY_ACCESS
    }

    pub open spec fn interp(self) -> Map<usize, PTE> {
        self.pt_mem@
    }

    pub open spec fn write(self, idx: usize, value: usize, r: MemRegion) -> WrappedMapTokenView {
        WrappedMapTokenView {
            regions: self.regions.insert(r, self.regions[r].update(idx as int, value)),
            pt_mem: self.pt_mem.write(add(r.base as usize, mul(idx, 8)), value),
            ..self
        }
    }

    pub proof fn lemma_interps_match(self, pt: PTDir)
        requires PT::inv(self, pt)
        ensures usize_keys(PT::interp(self, pt).interp().map) == self.interp()
    {
        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
        //assume(forall|k| PT::interp(self, pt).interp().map.contains_key(k) ==> k <= usize::MAX);
        assert forall|va, pte| #[trigger] PT::interp(self, pt).interp().map.contains_pair(va as nat, pte)
            implies self.pt_mem@.contains_pair(va, pte)
        by {
            admit();
        };
        assert forall|va, pte| self.pt_mem@.contains_pair(va, pte)
            implies #[trigger] PT::interp(self, pt).interp().map.contains_pair(va as nat, pte)
        by {
            admit();
        };
        admit();
        assert(usize_keys(PT::interp(self, pt).interp().map) =~= self.pt_mem@);
    }
}

pub tracked struct WrappedMapToken {
    tracked tok: Token,
    ghost done: bool,
    ghost orig_st: os::State,
    ghost regions: Set<MemRegion>,
}

impl WrappedMapToken {
    pub closed spec fn view(&self) -> WrappedMapTokenView {
        WrappedMapTokenView {
            orig_st: self.orig_st,
            args:
                (self.orig_st.core_states[self.tok.core()]->MapExecuting_vaddr as usize,
                 self.orig_st.core_states[self.tok.core()]->MapExecuting_pte),
            regions:
                Map::new(
                    |r: MemRegion| self.regions.contains(r),
                    |r: MemRegion| Seq::new(512, |i: int| self.tok.st().mmu@.pt_mem.mem[(r.base + i * 8) as usize])),
            pt_mem: self.tok.st().mmu@.pt_mem,
        }
    }

    pub proof fn new(tracked tok: Token) -> (tracked res: WrappedMapToken)
        requires
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is MapExecuting,
            tok.thread() == tok.st().core_states[tok.core()]->MapExecuting_ult_id,
            tok.st().core_states[tok.core()]->MapExecuting_vaddr <= usize::MAX,
            tok.steps().len() > 0,
            !tok.on_first_step(),
            tok.progress() is Ready,
            tok.st().mmu@.pending_maps === map![],
            tok.st().inv(tok.consts()),
        ensures
            res.inv(),
            res@.orig_st == tok.st(),
            res@.pt_mem == tok.st().mmu@.pt_mem,
            tok.st().core_states[tok.core()] matches os::CoreState::MapExecuting { vaddr, pte, .. }
                && res@.args == (vaddr as usize, pte),
    {
        let tracked t = WrappedMapToken { tok, done: false, orig_st: tok.st(), regions: arbitrary() };
        assume(t.inv_regions());
        assert(Map::new(
                |k| t.tok.st().mmu@.pt_mem@.contains_key(k) && !t@.orig_st.mmu@.pt_mem@.contains_key(k),
                |k| t.tok.st().mmu@.pt_mem@[k])
            =~= map![]);
        t
    }

    pub proof fn destruct(tracked self) -> (tracked tok: Token)
        requires
            self.inv(),
            // TODO: more, specifically some sequencing so we can guarantee the posts
        ensures
            tok.progress() is Ready,
            tok.steps() === seq![],
            true, // TODO: more stuff
            // TODO: is it okay to just have pending_maps be this thing? (I think so)
            //tok.st().mmu@.pending_maps
            //    == Map::new(
            //        |k| self@.pt_mem@.contains_key(k) && !self@.orig_st.mmu@.pt_mem@.contains_key(k),
            //        |k| self@.pt_mem@[k]),
    {
        admit();
        self.tok
    }

    pub closed spec fn inv(&self) -> bool {
        // OSSM invariant
        &&& self.tok.st().inv(self.tok.consts())
        // Other stuff
        &&& !self.tok.on_first_step()
        &&& self.tok.consts().valid_core(self.tok.core())
        &&& self.tok.consts().valid_ult(self.tok.thread())
        &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::MapExecuting { vaddr, pte, ult_id }
        &&& vaddr <= usize::MAX
        &&& self.tok.thread() == ult_id
        &&& self.tok.steps().len() > 0
        &&& self.tok.progress() is Ready
        &&& self.tok.st().mmu@.pending_maps
            == Map::new(
                |k| self.tok.st().mmu@.pt_mem@.contains_key(k) && !self.orig_st.mmu@.pt_mem@.contains_key(k),
                |k| self.tok.st().mmu@.pt_mem@[k])
        &&& self.inv_regions()
    }

    spec fn inv_regions(&self) -> bool {
        &&& forall|r| #[trigger] self.regions.contains(r) ==> aligned(r.base, 4096) && r.size == 4096
    }

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
            let vaddr = tok.tok.st().core_states[core]->MapExecuting_vaddr;
            let pte = tok.tok.st().core_states[core]->MapExecuting_pte;
            let post = os::State {
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };
            let read_result = mmu_tok.lbl()->Read_2;
            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().mmu, mmu_tok.lbl()));
            assert(os::step_ReadPTMem(tok.tok.consts(), tok.tok.st(), post, core, addr, read_result, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::ReadPTMem { core: core, paddr: addr, value: read_result }, RLbl::Tau));
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

    pub exec fn write_stutter(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, value: usize, r: Ghost<MemRegion>)
        requires
            old(tok)@.regions.contains_key(r@),
            r@.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 1,
            old(tok)@.read(idx, r@) & 1 == 0,
            // This precondition makes the abstraction kind of leaky but we want to use the MMU
            // interp here. Otherwise we'd have to take two PTDirs as arguments and also require
            // their preconditions just to express this.
            old(tok)@.write(idx, value, r@).interp() == old(tok)@.interp(),
        ensures
            tok@ == old(tok)@.write(idx, value, r@),
            tok.inv(),
    {
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);

        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            let post = os::State { mmu: mmu_tok.post(), ..tok.tok.st() };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().mmu, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().mmu, mmu::rl1::Step::WriteNonneg, mmu_tok.lbl()));
            assert(os::step_MapOpStutter(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapOpStutter { core: core, paddr: addr, value }, RLbl::Tau));
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
            assert(unchanged_state_during_concurrent_trs(state2, state3));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            assert(state3.mmu@.pending_maps === state1.mmu@.pending_maps);
        }
        assert(tok@.regions[r@] =~= old(tok)@.regions[r@].update(idx as int, value));
        assert forall|r2: MemRegion| r2 !== r@ implies tok@.regions[r2] =~= old(tok)@.regions[r2] by {
            // TODO: This would require disjointness invariant in `inv_regions` which would be
            // duplicated from the one we already have in the impl. Gotta find a better way of
            // doing this.
            admit();
        };
        assume(tok@.regions[r@] == tok@.regions[r@].update(idx as int, value));
        assert(tok@.regions =~= old(tok)@.regions.insert(r@, tok@.regions[r@].update(idx as int, value)));
        // TODO: this is unstable??? (it used to work)
        assume(tok.tok.st().core_states[core] == old(tok).tok.st().core_states[core]);
    }

    pub exec fn write_change(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, value: usize, r: Ghost<MemRegion>)
        requires
            old(tok)@.regions.contains_key(r@),
            r@.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 1,
            old(tok)@.read(idx, r@) & 1 == 0,
            !candidate_mapping_overlaps_existing_vmem_usize(old(tok)@.interp(), old(tok)@.args.0, old(tok)@.args.1),
            old(tok)@.write(idx, value, r@).interp() == old(tok)@.interp().insert(old(tok)@.args.0, old(tok)@.args.1),
        ensures
            tok@ == old(tok)@.write(idx, value, r@),
            tok.inv(),
    {
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);

        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        proof {
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            let vaddr = tok@.args.0 as nat;
            let pte = tok@.args.1;
            // TODO: ???
            admit();
            assert(tok.tok.st().core_states[core] is MapExecuting);
            assert(tok.tok.st().core_states[core] matches os::CoreState::MapExecuting { vaddr: v, pte: p, .. } && vaddr == v && pte == p);
            let new_cs = os::CoreState::MapDone { ult_id: tok.tok.thread(), vaddr, pte, result: Ok(()) };
            let post = os::State {
                core_states: tok.tok.st().core_states.insert(core, new_cs),
                mmu: mmu_tok.post(),
                ..tok.tok.st()
            };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().mmu, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().mmu, mmu::rl1::Step::WriteNonneg, mmu_tok.lbl()));
            assert(os::step_MapOpChange(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapOpChange { core: core, paddr: addr, value }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
            admit();
        }

        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
        let ghost state2 = tok.tok.st();

        proof {
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(unchanged_state_during_concurrent_trs(state2, state3));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            assert(state3.mmu@.pending_maps === state1.mmu@.pending_maps);
        }
        assert(tok@.regions[r@] =~= old(tok)@.regions[r@].update(idx as int, value));
        assert forall|r2: MemRegion| r2 !== r@ implies tok@.regions[r2] =~= old(tok)@.regions[r2] by {
            // TODO: This would require disjointness invariant in `inv_regions` which would be
            // duplicated from the one we already have in the impl. Gotta find a better way of
            // doing this.
            admit();
        };
        assume(tok@.regions[r@] == tok@.regions[r@].update(idx as int, value));
        assert(tok@.regions =~= old(tok)@.regions.insert(r@, tok@.regions[r@].update(idx as int, value)));
    }

    pub exec fn allocate(Tracked(tok): Tracked<&mut Self>, layer: usize) -> (res: MemRegionExec)
        requires
            old(tok).inv(),
        ensures
            true, // TODO: disjointness but disjoint from what?
            aligned(res.base as nat, 4096),
            res.size == 4096,
            res.base + 4096 <= MAX_PHYADDR, // TODO: unnecessary?
            !old(tok)@.regions.contains_key(res@), // TODO: This is weird. It's weak and should be
                                                   // subsumed by disjointness? (which isn't
                                                   // currently here but should be)
            tok@.regions === old(tok)@.regions.insert(res@, new_seq::<usize>(512nat, 0usize)),
            tok@.pt_mem == old(tok)@.pt_mem,
            tok@.args == old(tok)@.args,
            tok@.orig_st == old(tok)@.orig_st,
            tok.inv(),
    {
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        let tracked mut osext_tok = tok.tok.get_osext_token();
        proof {
            osext_tok.prophesy_allocate();
            let post = os::State { os_ext: osext_tok.post(), ..tok.tok.st() };
            assert(os::step_Allocate(tok.tok.consts(), tok.tok.st(), post, core, osext_tok.lbl()->Allocate_res, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::Allocate { core: core, res: osext_tok.lbl()->Allocate_res }, RLbl::Tau));
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
        assume(res.base + 4096 <= MAX_PHYADDR);
        assume(!old(tok)@.regions.contains_key(res@));
        proof {
            tok.regions = tok.regions.insert(res@);
        }
        // TODO: We may have to zero the page ourselves or alternatively allow spontaneous writes
        // to unallocated memory regions.
        assume(tok@.regions[res@] === new_seq::<usize>(512nat, 0usize));
        assert(tok@.regions =~= old(tok)@.regions.insert(res@, new_seq::<usize>(512nat, 0usize)));
        res
    }
}

pub exec fn register_step_and_acquire_lock(Tracked(tok): Tracked<&mut Token>, Ghost(vaddr): Ghost<nat>, Ghost(pte): Ghost<PTE>)
    requires
        os::step_Map_enabled(vaddr, pte),
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).consts().valid_core(old(tok).core()), // TODO: ??
        old(tok).st().core_states[old(tok).core()] is Idle,
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
        !tok.on_first_step(),
{
    let ghost state1 = tok.st();
    let ghost core = tok.core();
    let ghost pidx = tok.do_concurrent_trs();
    proof {
        // TODO: Need something similar to lemma_concurrent_trs to prove this even when we don't
        // hold the lock
        assume(tok.st().core_states[core] == state1.core_states[core]);
        assume(tok.st().inv(tok.consts()));
        assume(tok.st().mmu@.pt_mem.pml4 == old(tok).st().mmu@.pt_mem.pml4);
        //lemma_concurrent_trs(state1, tok.st(), tok.consts(), tok.core(), pidx);
        let state2 = tok.st();
        let new_cs = os::CoreState::MapWaiting { ult_id: tok.thread(), vaddr, pte };
        let new_sound = tok.st().sound && os::step_Map_sound(tok.st().interp_pt_mem(), tok.st().core_states.values(), vaddr, pte);
        let post = os::State {
            core_states: tok.st().core_states.insert(core, new_cs),
            sound: new_sound,
            ..tok.st()
        };
        let lbl = RLbl::MapStart { thread_id: tok.thread(), vaddr, pte };
        assert(os::step_MapStart(tok.consts(), tok.st(), post, core, lbl));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapStart { core: core }, lbl));
        tok.register_external_step(post);
        let state3 = tok.st();
        os_invariant::next_preserves_inv(tok.consts(), state2, state3, lbl);
        tok.do_concurrent_trs();
        let state4 = tok.st();
        //lemma_concurrent_trs(state3, state4, tok.consts(), tok.core(), pidx);
        assume(state4.core_states[core] == state3.core_states[core]);
        assume(state4.inv(tok.consts()));
        assume(state4.mmu@.pt_mem.pml4 == state3.mmu@.pt_mem.pml4);
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
        //assert(os_ext::step_AcquireLock(tok.st().os_ext, post.os_ext, tok.consts().os_ext(), osext_tok.lbl()));
        assert(os::step_MapOpStart(tok.consts(), tok.st(), post, core, RLbl::Tau));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapOpStart { core: core }, RLbl::Tau));
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



// TODO: For now, much of the Unmap stuff is just placeholders so we can call unmap again.

pub tracked struct WrappedUnmapToken {
    tracked tok: Token,
    ghost done: bool,
    ghost orig_st: os::State,
    ghost regions: Set<MemRegion>,
}

impl WrappedUnmapToken {
    // TODO: shouldn't be external_body
    #[verifier(external_body)]
    pub proof fn new(tracked tok: Token) -> (tracked res: WrappedUnmapToken) {
        unimplemented!()
    }

    pub proof fn destruct(tracked self) -> (tracked tok: Token) {
        admit();
        self.tok
    }

    pub exec fn read(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, r: Ghost<MemRegion>) -> (res: usize) {
        proof { admit(); }
        let addr = pbase + idx * 8;
        let ghost state1 = tok.tok.st();
        let ghost core = tok.tok.core();
        assert(core == tok.tok.consts().ult2core[tok.tok.thread()]);
        assert(tok.tok.consts().valid_core(core));
        let tracked mut mmu_tok = tok.tok.get_mmu_token();

        let res = mmu::rl3::code::read(Tracked(&mut mmu_tok), addr);

        res & MASK_NEG_DIRTY_ACCESS
    }

    pub exec fn write_stutter(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, value: usize, r: Ghost<MemRegion>) {
        proof { admit(); }
        let addr = pbase + idx * 8;
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
    }

    pub exec fn write_change(Tracked(tok): Tracked<&mut Self>, pbase: usize, idx: usize, value: usize, r: Ghost<MemRegion>) {
        proof { admit(); }
        let addr = pbase + idx * 8;
        let tracked mut mmu_tok = tok.tok.get_mmu_token();
        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
    }

    pub exec fn deallocate(Tracked(tok): Tracked<&mut Self>, layer: usize, region: MemRegionExec) {
        proof { admit(); }
        let tracked mut osext_tok = tok.tok.get_osext_token();
        os_ext::code::deallocate(Tracked(&mut osext_tok), region, layer)
    }
}

} // verus!
