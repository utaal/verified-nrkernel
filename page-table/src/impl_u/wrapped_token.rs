use vstd::prelude::*;

use crate::spec_t::mmu::WalkResult;
use crate::spec_t::os;
use crate::spec_t::os_invariant;
use crate::spec_t::mmu::{ self };
use crate::spec_t::os_ext;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ aligned, new_seq, bit, candidate_mapping_overlaps_existing_vmem };
use crate::spec_t::mmu::defs::{ MemRegionExec, MemRegion, PTE, MAX_PHYADDR };
use crate::spec_t::mmu::translation::{ MASK_NEG_DIRTY_ACCESS };
use crate::theorem::RLbl;
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::os_code_vc::Token;
#[cfg(verus_keep_ghost)]
use crate::spec_t::os_code_vc::{ lemma_concurrent_trs, unchanged_state_during_concurrent_trs, lemma_concurrent_trs_no_lock };
use crate::impl_u::l2_impl::{ PT, PTDir };

use super::l1;
use super::l1::Directory;

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
    pub done: bool,
    pub regions: Map<MemRegion, Seq<usize>>,
    /// We also keep the flat memory directly because this is what the MMU's interpretation is
    /// defined on.
    pub pt_mem: mmu::pt_mem::PTMem,
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
            done: change,
            ..self
        }
    }

    //pub proof fn lemma_interps_match2(self, pt: PTDir)
    //    requires PT::inv(self, pt)
    //    ensures usize_keys(PT::interp(self, pt).interp().map) == self.interp()
    //{
    //    reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
    //    //assume(forall|k| PT::interp(self, pt).interp().map.contains_key(k) ==> k <= usize::MAX);
    //    assert forall|va, pte| #[trigger] PT::interp(self, pt).interp().map.contains_pair(va as nat, pte)
    //        implies self.pt_mem@.contains_pair(va, pte)
    //    by {
    //        admit();
    //    };
    //    assert forall|va, pte| self.pt_mem@.contains_pair(va, pte)
    //        implies #[trigger] PT::interp(self, pt).interp().map.contains_pair(va as nat, pte)
    //    by {
    //        admit();
    //    };
    //    admit();
    //    assert(usize_keys(PT::interp(self, pt).interp().map) =~= self.pt_mem@);
    //}

    pub proof fn lemma_interps_match(self, pt: PTDir)
        requires PT::inv(self, pt)
        ensures PT::interp(self, pt).interp() == crate::spec_t::mmu::defs::nat_keys(self.interp())
    {
        admit();
        
        // TODO(andrea): this is a sketch
        // MB: Some lemmas that may be useful:
        // * spec_t::mmu::rl2::lemma_pt_walk_result_vbase_equal
        // * spec_t::mmu::rl2::lemma_pt_walk_with_indexing_bits_match
        // * spec_t::mmu::rl2::lemma_indexing_bits_match_len_decrease
        // * spec_t::mmu::rl2::lemma_pt_walk_result_vaddr_indexing_bits_match
        // * spec_t::mmu::rl2::lemma_bits_align_to_usize
        // * spec_t::mmu::pt_mem::lemma_pt_walk
        // * spec_t::mmu::pt_mem::lemma_pt_walk_agrees_in_frame
        //
        // These may help with going from PT::interp(..) to PT::interp(..).interp()
        // (But probably only necessary with the alternative strategy)
        // * impl_u::l1::lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping
        // * impl_u::l1::lemma_interp_aux_contains_implies_interp_of_entry_contains
        // * impl_u::l1::lemma_interp_contains_implies_interp_of_entry_contains
        //
        // For the alternative strategy I mentioned on Zulip:
        // (I think your current strategy is probably easier if it works though)
        // * lemma_iter_walk_equals_pt_walk

        reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
        reveal_with_fuel(PT::interp_at, 10);
        reveal_with_fuel(PT::interp_at_aux, 10);
        reveal_with_fuel(PT::interp_at_entry, 10);
        reveal_with_fuel(PT::inv_at, 10);
        
        let root_dir = crate::impl_u::l1::Directory {
            entries: PT::interp_at_aux(self, pt, 0, self.pt_mem.pml4, 0, seq![]),
            layer: 0,
            base_vaddr: 0,
            arch: mmu::defs::x86_arch_spec,
        };

        assert(PT::interp_at(self, pt, 0, self.pt_mem.pml4, 0) == root_dir);
        
        assert(PT::interp_at_aux(self, pt, 0, self.pt_mem.pml4, 0, seq![]) == 
            {
                let entry = PT::interp_at_entry(self, pt, 0, self.pt_mem.pml4, 0, 0 /* init.len() */);
                PT::interp_at_aux(self, pt, 0, self.pt_mem.pml4, 0, seq![].push(entry))
            });

        assert forall|k: nat| k <= usize::MAX implies (
            self.pt_mem@.contains_key(k as usize) == root_dir.interp().contains_key(k)) by {
            
            let walk = self.pt_mem.pt_walk(k as usize);
            assert(walk.complete);
            if self.pt_mem@.contains_key(k as usize) {
                assert(walk.path.last().1 is Page);
                if walk.path.len() == 1 {
                    assert(false);
                } else if walk.path.len() == 2 {
                    let l1_pt_entry = PT::entry_at_spec(self, pt, 0, self.pt_mem.pml4, walk.path[0].0 as nat);
                    assert(walk.path[0].1 == l1_pt_entry@);
                    assert(l1_pt_entry@ is Directory);
                    let l1_pt = PT::interp_at_entry(self, pt, 0, self.pt_mem.pml4, 0, walk.path[0].0 as nat);
                    assert(PT::inv_at(self, pt, 0, self.pt_mem.pml4));
                    assert(l1_pt is Directory);
                    let l2_pt_entry = PT::entry_at_spec(self, pt.entries[walk.path[0].0 as int].unwrap(), 1, self.pt_mem.pml4, walk.path[1].0 as nat);
                    assert(walk.path[1].1 == l2_pt_entry@);
                    let l2_pt = PT::interp_at_entry(self, pt.entries[walk.path[0].0 as int].unwrap(), 1, self.pt_mem.pml4, l1_pt_entry@->Directory_addr as nat, walk.path[1].0 as nat);
                    assert(root_dir.interp().contains_key(k));
                } else if walk.path.len() == 3 {
                    assert(root_dir.interp().contains_key(k));
                } else if walk.path.len() == 4 {
                    assert(root_dir.interp().contains_key(k));
                }
                assert(self.pt_mem@.contains_key(k as usize) == root_dir.interp().contains_key(k));
            } else {
                assert(!root_dir.interp().contains_key(k));
            }

            // WalkResult::Valid { vbase, pte } => {}
            // WalkResult::Invalid { vaddr } => {}
        }

        assert forall|k: nat| k <= usize::MAX && #[trigger] self.pt_mem@.contains_key(k as usize) implies PT::interp_at(self, pt, 0, self.pt_mem.pml4, 0).interp().contains_pair(k, self.pt_mem@[k as usize]) by {
            admit();
        }

        assert(PT::interp_at(self, pt, 0, self.pt_mem.pml4, 0).interp() == 
            Map::new(|k: nat| k <= usize::MAX && self.pt_mem@.contains_key(k as usize), |k: nat| self.pt_mem@[k as usize]));

        assert(PT::interp(self, pt).interp() =~= crate::spec_t::mmu::defs::nat_keys(self.interp()));
    }
}

pub tracked struct WrappedMapToken {
    tracked tok: Token,
    ghost done: bool,
    ghost orig_st: os::State,
    ghost regions: Set<MemRegion>,
    //ghost prophesied_result: Result<(),()>,
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
            done: self.done,
            regions:
                Map::new(
                    |r: MemRegion| self.regions.contains(r),
                    |r: MemRegion| Seq::new(512, |i: int| self.tok.st().mmu@.pt_mem.mem[(r.base + i * 8) as usize])),
            pt_mem: self.tok.st().mmu@.pt_mem,
        }
    }

    pub proof fn new(tracked tok: Token) -> (tracked res: WrappedMapToken)
        requires
            //proph_res.may_resolve(),
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is MapExecuting,
            tok.thread() == tok.st().core_states[tok.core()]->MapExecuting_ult_id,
            tok.st().core_states[tok.core()]->MapExecuting_vaddr <= usize::MAX,
            tok.steps().len() == 1,
            //tok.steps() ===
            //    seq![RLbl::MapEnd {
            //        thread_id: tok.thread(),
            //        vaddr: tok.st().core_states[tok.core()]->MapExecuting_vaddr,
            //        result: prophesied_result,
            //    }],
            !tok.on_first_step(),
            tok.progress() is Ready,
            //tok.st().mmu@.pending_maps === map![],
            tok.st().inv(tok.consts()),
        ensures
            res.inv(),
            res@.orig_st == tok.st(),
            res@.pt_mem == tok.st().mmu@.pt_mem,
            tok.st().core_states[tok.core()] matches os::CoreState::MapExecuting { vaddr, pte, .. }
                && res@.args == (OpArgs::Map { base: vaddr as usize, pte }),
            !res@.done,
    {
        let tracked t = WrappedMapToken { tok, done: false, orig_st: tok.st(), regions: arbitrary() };
        assume(t.inv_regions());
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
        &&& self.inv_regions()
        &&& self.tok.steps().len() == 1
        &&& if self.done {
            &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::MapDone { vaddr, pte, ult_id, result }
            &&& vaddr <= usize::MAX
            &&& self.tok.thread() == ult_id
            &&& self@.args == OpArgs::Map { base: vaddr as usize, pte }
            //&&& self.tok.st().mmu@.pending_maps === if result is Ok { map![vaddr as usize => pte] } else { map![] }
        } else {
            &&& self.tok.st().core_states[self.tok.core()] matches os::CoreState::MapExecuting { vaddr, pte, ult_id }
            &&& self.tok.thread() == ult_id
            &&& vaddr <= usize::MAX
            &&& self@.args == OpArgs::Map { base: vaddr as usize, pte }
            //&&& self.proph_res.may_resolve()
            //&&& self.tok.steps() === seq![RLbl::MapEnd { thread_id: self.tok.thread(), vaddr, result: self.proph_res.value() }]
            //&&& self.tok.st().mmu@.pending_maps === map![]
        }
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
            !old(tok)@.done,
            old(tok)@.regions.contains_key(r),
            r.base == pbase,
            idx < 512,
            old(tok).inv(),
            value & 1 == 1,
            old(tok)@.read(idx, r) & 1 == 0,
            PT::inv(old(tok)@, root_pt1),
            PT::inv(old(tok)@.write(idx, value, r, false), root_pt2),
            PT::interp_to_l0(old(tok)@.write(idx, value, r, false), root_pt2) == PT::interp_to_l0(old(tok)@, root_pt1),
            // This precondition makes the abstraction kind of leaky but we want to use the MMU
            // interp here. Otherwise we'd have to take two PTDirs as arguments and also require
            // their preconditions just to express this.
            //old(tok)@.write(idx, value, r, false).interp() == old(tok)@.interp(),
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
            old(tok)@.write(idx, value, r, false).lemma_interps_match(root_pt2);
            broadcast use to_rl1::next_refines;
            assert(!state1.mmu@.writes.tso.is_empty() ==> core == state1.mmu@.writes.core);
            mmu_tok.prophesy_write(addr, value);
            let post = os::State { mmu: mmu_tok.post(), ..tok.tok.st() };

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().mmu, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().mmu, mmu::rl1::Step::WriteNonneg, mmu_tok.lbl()));
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
            assert(unchanged_state_during_concurrent_trs(state2, state3));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            //assert(state3.mmu@.pending_maps === state2.mmu@.pending_maps);
            //assert(state3.mmu@.pending_maps === state1.mmu@.pending_maps) by {
            //    // TODO: Annoying because of mismatch between nat/usize maps
            //    admit();
            //};
            assert(tok.inv());
            // unstable somehow
            assume(tok.tok.st().core_states[core] == old(tok).tok.st().core_states[core]);
            assert(tok@.regions[r] =~= old(tok)@.regions[r].update(idx as int, value));
            assert forall|r2: MemRegion| r2 !== r implies tok@.regions[r2] =~= old(tok)@.regions[r2] by {
                // TODO: This would require disjointness invariant in `inv_regions` which would be
                // duplicated from the one we already have in the impl. Gotta find a better way of
                // doing this.
                admit();
            };
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
            !old(tok)@.done,
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

            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().mmu, mmu_tok.lbl()));
            assert(mmu::rl1::next_step(tok.tok.st().mmu@, post.mmu@, tok.tok.consts().mmu, mmu::rl1::Step::WriteNonneg, mmu_tok.lbl()));
            old(tok)@.lemma_interps_match(root_pt);
            old(tok)@.write(idx, value, r, true).lemma_interps_match(root_pt);
            //assert(PT::interp(old(tok)@, root_pt).interp().map == crate::spec_t::mmu::defs::nat_keys(old(tok)@.pt_mem@));
            //assert(crate::spec_t::mmu::defs::nat_keys(post.mmu@.pt_mem@) == post.interp_pt_mem());
            //assert(crate::spec_t::mmu::defs::nat_keys(tok@.pt_mem@) == tok.tok.st().interp_pt_mem());
            //assert(post.interp_pt_mem() == tok.tok.st().interp_pt_mem().insert(vaddr, pte));
            assert(os::step_MapOpChange(tok.tok.consts(), tok.tok.st(), post, core, addr, value, RLbl::Tau));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapOpChange { core, paddr: addr, value }, RLbl::Tau));
            tok.tok.register_internal_step_mmu(&mut mmu_tok, post);
            os_invariant::next_preserves_inv(tok.tok.consts(), state1, tok.tok.st(), RLbl::Tau);
        }

        mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
        let ghost state2 = tok.tok.st();
        proof { tok.done = true; }

        proof {
            assert(state1.os_ext.lock == Some(core));
            tok.tok.return_mmu_token(mmu_tok);
            let pidx = tok.tok.do_concurrent_trs();
            let state3 = tok.tok.st();
            lemma_concurrent_trs(state2, state3, tok.tok.consts(), tok.tok.core(), pidx);
            assert(unchanged_state_during_concurrent_trs(state2, state3));
            assert(state2.mmu@.pt_mem == state1.mmu@.pt_mem.write(add(pbase, mul(idx, 8)), value));
            //assert(state3.mmu@.pending_maps === state2.mmu@.pending_maps);
            //assert(state3.mmu@.pending_maps === state1.mmu@.pending_maps.insert(vaddr, pte)) by {
            //    // TODO: Annoying because of mismatch between nat/usize maps
            //    reveal(pt_mem::PTMem::view);
            //    admit();
            //};
            //assert(tok.tok.st().mmu@.pending_maps.submap_of(map![vaddr => pte]));
            assert(tok.inv());
        }
        assert(tok@.regions[r] =~= old(tok)@.regions[r].update(idx as int, value));
        assert forall|r2: MemRegion| r2 !== r implies tok@.regions[r2] =~= old(tok)@.regions[r2] by {
            // TODO: This would require disjointness invariant in `inv_regions` which would be
            // duplicated from the one we already have in the impl. Gotta find a better way of
            // doing this.
            admit();
        };
        assert(tok@.pt_mem == old(tok)@.pt_mem.write(add(r.base as usize, mul(idx, 8)), value));
        assert(tok@.regions =~= old(tok)@.regions.insert(r, old(tok)@.regions[r].update(idx as int, value)));
        assert(tok@ =~= old(tok)@.write(idx, value, r, true));
    }

    pub exec fn allocate(Tracked(tok): Tracked<&mut Self>, layer: usize) -> (res: MemRegionExec)
        requires
            !old(tok)@.done,
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
            !tok@.done,
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
        assume(res.base + 4096 <= MAX_PHYADDR);
        assume(!old(tok)@.regions.contains_key(res@));
        proof {
            tok.regions = tok.regions.insert(res@);
        }
        // TODO: We may have to zero the page ourselves or alternatively allow spontaneous writes
        // to unallocated memory regions. (Or require zeroed pages when deallocating.)
        assume(tok@.regions[res@] === new_seq::<usize>(512nat, 0usize));
        assert(tok@.regions =~= old(tok)@.regions.insert(res@, new_seq::<usize>(512nat, 0usize)));
        res
    }

    /// If there's an overlapping mapping we don't write anything but just do a MapNoOp step.
    pub proof fn register_failed_map(tracked tok: &mut Self, root_pt: PTDir)
        requires
            !old(tok)@.done,
            old(tok).inv(),
            candidate_mapping_overlaps_existing_vmem(
                PT::interp_to_l0(old(tok)@, root_pt),
                old(tok)@.args->Map_base as nat,
                old(tok)@.args->Map_pte
            ),
            PT::inv(old(tok)@, root_pt),
        ensures
            tok@ == (WrappedTokenView { done: true, ..old(tok)@ }),
            tok.inv(),
    {
        tok@.lemma_interps_match(root_pt);
        tok.done = true;

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

    pub exec fn finish_map_and_release_lock(
        Tracked(tok): Tracked<WrappedMapToken>,
        //Tracked(proph_res): Tracked<Prophecy<Result<(),()>>>
    ) -> (rtok: Tracked<Token>)
        requires
            tok@.done,
            tok.inv(),
            //proph_res.may_resolve(),
            //tok.tok.steps() ===
            //    seq![RLbl::MapEnd {
            //       thread_id: tok.tok.thread(),
            //       vaddr: tok.tok.st().core_states[tok.tok.core()]->MapDone_vaddr,
            //       result: proph_res.value()
            //    }],
        ensures
            //proph_res.value() == arbitrary()
            rtok@.progress() is Unready,
            rtok@.steps() === seq![],
            true, // TODO: more stuff?
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
            assert(mmu::rl3::next(tok.tok.st().mmu, post.mmu, tok.tok.consts().mmu, mmu_tok.lbl()));
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
            assert(os_ext::step_ReleaseLock(tok.tok.st().os_ext, post.os_ext, tok.tok.consts().os_ext(), osext_tok.lbl()));
            let lbl = RLbl::MapEnd { thread_id: tok.tok.thread(), vaddr, result };
            // TODO: Need some help here from the invariant and resolve the prophecy before we take
            // the step. Prophecy is actually problematic here.
            assume(lbl == tok.tok.steps()[0]);
            assert(os::step_MapEnd(tok.tok.consts(), tok.tok.st(), post, core, lbl));
            assert(os::next_step(tok.tok.consts(), tok.tok.st(), post, os::Step::MapEnd { core }, lbl));
            tok.tok.register_external_step_osext(&mut osext_tok, post);
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
}

pub exec fn start_map_and_acquire_lock(Tracked(tok): Tracked<&mut Token>, Ghost(vaddr): Ghost<nat>, Ghost(pte): Ghost<PTE>)
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
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapStart { core: core }, lbl));
        tok.register_external_step(post);
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



pub tracked struct WrappedUnmapToken {
    tracked tok: Token,
    ghost done: bool,
    ghost orig_st: os::State,
    ghost regions: Set<MemRegion>,
}

impl WrappedUnmapToken {
    pub closed spec fn view(&self) -> WrappedTokenView {
        WrappedTokenView {
            orig_st: self.orig_st,
            args:
                OpArgs::Unmap {
                    base: self.orig_st.core_states[self.tok.core()]->UnmapExecuting_vaddr as usize,
                },
            done: self.done,
            regions:
                Map::new(
                    |r: MemRegion| self.regions.contains(r),
                    |r: MemRegion| Seq::new(512, |i: int| self.tok.st().mmu@.pt_mem.mem[(r.base + i * 8) as usize])),
            pt_mem: self.tok.st().mmu@.pt_mem,
        }
    }

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
