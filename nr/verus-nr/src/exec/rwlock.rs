#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{
    prelude::*,
    cell::{PCell, PointsTo},
    atomic_ghost::{AtomicBool, AtomicU64},
    atomic_with_ghost
};

use crate::spec::rwlock::RwLockSpec;
use crate::exec::CachePadded;

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// RwLockWriteGuard
////////////////////////////////////////////////////////////////////////////////////////////////////

/// structure used to release the exclusive write access of a lock when dropped.
//
/// This structure is created by the write and try_write methods on RwLockSpec.
pub tracked struct RwLockWriteGuard<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)] T> {
    handle:  Tracked<RwLockSpec::exc_guard<PointsTo<T>>>,
    cell_perms:  Tracked<PointsTo<T>>
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//  RwLockReadGuard
////////////////////////////////////////////////////////////////////////////////////////////////////

/// RAII structure used to release the shared read access of a lock when dropped.
///
/// This structure is created by the read and try_read methods on RwLockSpec.
pub struct RwLockReadGuard<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)]T> {
    tid: usize,
    perms: Ghost<PointsTo<T>>,
    handle: Tracked<RwLockSpec::shared_guard<PointsTo<T>>>,
}

impl<T> RwLockReadGuard<T> {
    pub closed spec fn view(&self) -> T {
        self.handle@@.key.1.view().value.get_Some_0()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// RwLockDist Impl
////////////////////////////////////////////////////////////////////////////////////////////////////

pub const MAX_RC: u64 =  0xffff_ffff_ffff_fff0;

#[verifier(external_body)] /* vattr */
pub fn panic_with_ref_count_too_big() {
    panic!("WARNING: Tail value exceeds the maximum value of u64.");
}

struct_with_invariants!{
    pub struct RwLock<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)] T> {
        /// cell containing the data
        data: PCell<T>,
        /// flag indicating whether the writer lock is held or being acquired
        exc_locked: CachePadded<AtomicBool<_, RwLockSpec::exc_locked<PointsTo<T>>, _>>,
        /// map of readers that want to acquire the reader lock
        ref_counts: Vec<CachePadded<AtomicU64<_, RwLockSpec::ref_counts<PointsTo<T>>, _>>>,
        /// the spec instance
        inst: Tracked<RwLockSpec::Instance<PointsTo<T>>>,
        user_inv: Ghost<Set<T>>,
    }

    pub closed spec fn wf(&self) -> bool {

        predicate {
            &&& self.inst@.rc_width() == self.ref_counts@.len()
            // &&& self.ref_counts@.len() > 0

            &&& forall |i: int| #![trigger self.ref_counts@.index(i)] (0 <= i && i < self.ref_counts@.len()) ==>
                self.ref_counts@.index(i).0.well_formed()
                && self.ref_counts@.index(i).0.constant() === (self.inst, i)

            &&& forall |v: PointsTo<T>| #[trigger] self.inst@.user_inv().contains(v) == (
                equal(v@.pcell, self.data.id()) && v@.value.is_Some()
                        && self.user_inv@.contains(v@.value.get_Some_0())
            )
        }

        invariant on exc_locked with (inst) specifically (self.exc_locked.0) is (b: bool, g: RwLockSpec::exc_locked<PointsTo<T>>) {
            g@.instance == inst@
            && g@.value == b
        }

        invariant on ref_counts with (inst)
            forall |i: int|
            where (0 <= i < self.ref_counts@.len())
            specifically (self.ref_counts@[i].0)
            is (v: u64, g: RwLockSpec::ref_counts<PointsTo<T>>)
        {
            g@.instance == inst@
            && g@.key == i
            && g@.value == v as int
            && g@.value <= MAX_RC
        }
    }
}

#[verifier(external_body)] /* vattr */
pub fn panic_with_value_too_big() {
    panic!("WARNING: Tail value exceeds the maximum value of u64.");
}


impl<T> RwLock<T> {

    /// Invariant on the data
    pub closed spec fn inv(&self, t: T) -> bool {
        self.user_inv@.contains(t)
    }

    pub open spec fn thread_id_valid(&self, t: nat) -> bool {
        0 <= t && t < self.max_threads()
    }

    pub closed spec fn max_threads(&self) -> nat {
        self.ref_counts@.len()
    }


    pub closed spec fn wf_read_handle(&self, read_handle: &RwLockReadGuard<T>) -> bool {
        &&& self.thread_id_valid(read_handle.tid as nat)
        &&& read_handle.handle@@.instance == self.inst
        &&& read_handle.handle@@.count == 1
        &&& read_handle.handle@@.key == (read_handle.tid as int, read_handle.perms@)
        &&& read_handle.perms@@.pcell == self.data.id()
        &&& read_handle.perms@@.value.is_Some()
    }

    pub closed spec fn wf_write_handle(&self, write_handle: &RwLockWriteGuard<T>) -> bool {
        &&& write_handle.handle@@.instance == self.inst
        &&& write_handle.cell_perms@@.pcell == self.data.id()
        &&& write_handle.cell_perms@@.value.is_None()
    }

    #[verifier(spinoff_prover)]
    pub fn new(rc_width: usize, t: T, inv: Ghost<FnSpec(T) -> bool>) -> (s: Self)
        requires
            0 < rc_width,
            inv@(t)
        ensures s.wf(), forall |v: T| s.inv(v) == inv@(v), s.max_threads() == rc_width
    {
        let tracked inst;
        let tracked exc_locked_token;
        let tracked mut ref_counts_tokens;

        // create the pcell object
        let (pcell_data, Tracked(mut pcell_token)) = PCell::new(t);

        // create the set of allowed data structures
        let ghost set_inv = Set::new(inv@);
        let ghost user_inv = Set::new(|s: PointsTo<T>| {
            &&& equal(s@.pcell, pcell_data.id())
            &&& s@.value.is_Some()
            &&& set_inv.contains(s@.value.get_Some_0())
        });

        proof {
            // user_inv: Set<T>, t: T
            // initialize_full(user_inv, perm@, Option::Some(perm.get()));
            //
            // initialize(rc_width: int, init_t: T, user_inv: Set<T>,) {
            let tracked (Tracked(inst0), Tracked(exc_locked_token0), Tracked(ref_counts_tokens0), _, _, _, _) =
                RwLockSpec::Instance::initialize(rc_width as int,  pcell_token, user_inv, Option::Some(pcell_token));
            inst = inst0;
            exc_locked_token = exc_locked_token0;
            ref_counts_tokens = ref_counts_tokens0;
        }

        let tracked_inst: Tracked<RwLockSpec::Instance<PointsTo<T>>> = Tracked(inst.clone());
        let exc_locked_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(exc_locked_token));

        let mut v: Vec<CachePadded<AtomicU64<(Tracked<RwLockSpec::Instance<PointsTo<T>>>, int), RwLockSpec::ref_counts<PointsTo<T>>, _>>>
            = Vec::new();
        let mut i: usize = 0;

        assert forall |j: int|
            i <= j && j < rc_width implies
            #[trigger] ref_counts_tokens.dom().contains(j)
                  && equal(ref_counts_tokens.index(j)@.instance, inst)
                  && equal(ref_counts_tokens.index(j)@.key, j)
                  && equal(ref_counts_tokens.index(j)@.value, 0)
        by {
            assert(ref_counts_tokens.dom().contains(j));
            assert(equal(ref_counts_tokens.index(j)@.instance, inst));
            assert(equal(ref_counts_tokens.index(j)@.key, j));
            assert(equal(ref_counts_tokens.index(j)@.value, 0));
        }

        assert(forall |j: int|
          #![trigger( ref_counts_tokens.dom().contains(j) )]
          #![trigger( ref_counts_tokens.index(j) )]
            i <= j && j < rc_width ==> (
            ref_counts_tokens.dom().contains(j)
            && equal(ref_counts_tokens.index(j)@.instance, inst)
            && equal(ref_counts_tokens.index(j)@.key, j)
            && equal(ref_counts_tokens.index(j)@.value, 0)
        ));

        while i < rc_width
            invariant
                i <= rc_width,
                v@.len() == i as int,
                forall|j: int| #![trigger v@.index(j)] 0 <= j && j < i ==>
                    v@.index(j).0.well_formed()
                      && equal(v@.index(j).0.constant(), (tracked_inst, j)),
                tracked_inst@ == inst,
                forall |j: int|
                    #![trigger( ref_counts_tokens.dom().contains(j) )]
                    #![trigger( ref_counts_tokens.index(j) )]
                    i <= j && j < rc_width ==> (
                        ref_counts_tokens.dom().contains(j)
                        && equal(ref_counts_tokens.index(j)@.instance, inst)
                        && equal(ref_counts_tokens.index(j)@.key, j)
                        && equal(ref_counts_tokens.index(j)@.value, 0)
                    ),
        {
            assert(ref_counts_tokens.dom().contains(i as int));

            let tracked ref_count_token = ref_counts_tokens.tracked_remove(i as int);

            let rc_atomic = AtomicU64::new(Ghost((tracked_inst, i as int)), 0, Tracked(ref_count_token));
            v.push(CachePadded(rc_atomic));

            i = i + 1;

            assert forall |j: int|
                i <= j && j < rc_width implies
                #[trigger] ref_counts_tokens.dom().contains(j)
                      && equal(ref_counts_tokens.index(j)@.instance, inst)
                      && equal(ref_counts_tokens.index(j)@.key, j)
                      && equal(ref_counts_tokens.index(j)@.value, 0)
            by {
                assert(ref_counts_tokens.dom().contains(j));
                assert(equal(ref_counts_tokens.index(j)@.instance, inst));
                assert(equal(ref_counts_tokens.index(j)@.key, j));
                assert(equal(ref_counts_tokens.index(j)@.value, 0));
            }
        }

        let s = RwLock {
            user_inv: Ghost(set_inv),
            data: pcell_data,
            inst: Tracked(inst),
            exc_locked: CachePadded(exc_locked_atomic),
            ref_counts: v,
        };

        assert(s.inst@.rc_width() == s.ref_counts@.len());

        s
    }


    pub fn acquire_write(&self) -> (res: (T, Tracked<RwLockWriteGuard<T>>))
        requires
            self.wf()
        ensures
            self.wf(),
            self.wf_write_handle(&res.1@) && self.inv(res.0)
    {
        // -----------------------------------------------------------------------------------------
        // First: acquire the write lock
        // -----------------------------------------------------------------------------------------
        let tracked mut token : Option<RwLockSpec::exc_pending<PointsTo<T>>> = None;
        let mut acquired = false;
        while !acquired
            invariant
                self.wf(),
                acquired ==> token.is_Some() && token.get_Some_0()@.instance == self.inst && token.get_Some_0()@.value == 0
        {
            let result = atomic_with_ghost!(
                &self.exc_locked.0 => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res.is_Ok() {
                    token = Option::Some(self.inst.borrow().exc_start(&mut g));
                }
            });
            acquired = result.is_ok();
        }

        let tracked mut token = token.tracked_unwrap();

        // -----------------------------------------------------------------------------------------
        // Next: wait until all readers have released their lock
        // -----------------------------------------------------------------------------------------

        let mut idx = 0;
        while idx < self.ref_counts.len()
            invariant
                self.wf(),
                idx <= self.ref_counts.len(),
                token@.instance == self.inst,
                token@.value == idx
        {

            // wait until the reader hasn't taken the reader lock yet
            let mut taken = true;
            while taken
                invariant
                    self.wf(),
                    idx < self.ref_counts.len(),
                    token@.instance == self.inst,
                    taken ==> token@.value == idx,
                    !taken ==> token@.value == idx + 1
            {
                let result = atomic_with_ghost!(
                    &self.ref_counts[idx].0 => load();
                    returning res;
                    ghost g => {
                    if res == 0 {
                        token = self.inst.borrow().exc_check_count(&g, token);
                    }
                });
                taken = result != 0;
            }
            idx = idx + 1;
        }

        // (Ghost<Option<PointsTo<T>>>, Tracked<T>, Tracked<exc_guard<T>>>)
        let tracked (_, Tracked(cell_perms), handle) = self.inst.borrow().exc_finish(token);

        // obtain the data
        let t = self.data.take(Tracked(&mut cell_perms));

        // return the Writer Guard
        (t , Tracked(RwLockWriteGuard { handle, cell_perms: Tracked(cell_perms) }))
    }


    pub fn acquire_read<'a>(&'a self, tid: usize) -> (res: RwLockReadGuard<T>)
        requires
            self.wf(), self.thread_id_valid(tid as nat)
        ensures
            self.wf(), self.wf_read_handle(&res), self.inv(res@)

    {
        loop
            invariant
                self.wf(),
                tid < self.ref_counts.len()
        {
            // TODO: figure out how to do the optimized read here!
            let rc = atomic_with_ghost!(
                &self.ref_counts[tid].0 => load();
                returning rc;
                ghost g => { }
            );

            if rc == MAX_RC {
                panic_with_ref_count_too_big();
                ////////////////////////////////////////////////////////////////////////////////////
                // !!! THIS IS A PANIC CASE! WE DO NOT RETURN FROM HERE !!!
                ////////////////////////////////////////////////////////////////////////////////////
                #[allow(while_true)]
                while true {} // TODO: is that fine?
            }

            // fetch add on the reader lock
            // let tracked mut ref_counts : Tracked<RwLockSpec::ref_counts<PointsTo<T>>>;
            let tracked mut shared_pending: Option<RwLockSpec::shared_pending<PointsTo<T>>>;
            let res = atomic_with_ghost!(
                &self.ref_counts[tid].0 => compare_exchange(rc, rc+1);
                update prev->next;
                ghost g =>
            {
                if prev == rc {
                    assert(rc < MAX_RC);
                    // Tracked<ref_counts<T>>,Tracked<shared_pending<T>>
                    let tracked (_ref_counts, _shared_pending) = self.inst.borrow().shared_start(tid as int, g);
                    // ref_counts = _ref_counts;
                    shared_pending = Some(_shared_pending.get());
                    g = _ref_counts.get();

                    // assert(g@.value <= MAX_RC);
                } else {
                    shared_pending = None;
                }

                // assume(g@.value < MAX_RC);
                // // Tracked<ref_counts<T>>,Tracked<shared_pending<T>>
                // let tracked (_ref_counts, _shared_pending) = self.inst.borrow().shared_start(tid as int, g);
                // // ref_counts = _ref_counts;
                // shared_pending = Some(_shared_pending.get());
                // g = _ref_counts.get();

                // assert(g@.instance == self.inst@);
                // assert(g@.key == tid as nat);
            });

            if res.is_err() {
                continue;
            }

            // exc_locked: CachePadded<AtomicBool<_, RwLockSpec::exc_locked<PointsTo<T>>, _>>,
            let ghost mut perms : PointsTo<T>;
            let tracked shared_guard : Option<RwLockSpec::shared_guard<PointsTo<T>>>;
            let is_exc_locked = atomic_with_ghost!(
                &self.exc_locked.0 => load();
                returning res;
                ghost g => {
                if !res {
                    let tracked (_perms, _shared_guard) = self.inst.borrow().shared_finish(tid as int, &g, shared_pending.tracked_unwrap());
                    perms = _perms@.unwrap();
                    shared_guard = Some(_shared_guard.get());
                    shared_pending = None;
                } else {
                    shared_guard = None;
                }
            });

            let perms = Ghost(perms);

            if is_exc_locked {
                // writer lock still held, try again
                let res = atomic_with_ghost!(
                    &self.ref_counts[tid].0 => fetch_sub(1);
                    ghost g =>
                {
                    let tracked shared_pending = shared_pending.tracked_unwrap();
                    self.inst.borrow().rc_not_zero_guard(tid as int, &g, &shared_pending);

                    g = self.inst.borrow().shared_abandon(tid as int, g, shared_pending);
                });
            } else {
                // create the read guard lock
                return RwLockReadGuard { tid, perms, handle: Tracked(shared_guard.tracked_unwrap()) };
            }
        }
    }

    pub fn borrow<'a>(&'a self, read_handle: Tracked<&'a RwLockReadGuard<T>>) -> (res: &'a T)
        requires self.wf() && self.wf_read_handle(&read_handle@)
        ensures res == read_handle@@
    {
        let ghost val = (read_handle@.tid as int, read_handle@.perms@);
        let tracked handle = read_handle.borrow().handle.borrow();
        let tracked perm = self.inst.borrow().do_guard(val, &handle);
        self.data.borrow(Tracked(&perm))
    }


    pub fn release_write(&self, val: T, write_handle: Tracked<RwLockWriteGuard<T>>)
        requires
            self.wf(),
            self.wf_write_handle(&write_handle@),
            self.inv(val)
        ensures
            self.wf()
    {
        let tracked RwLockWriteGuard { cell_perms, handle } = write_handle.get();
        let tracked mut cell_perms = cell_perms.get();

        self.data.put(Tracked(&mut cell_perms), val);


        let res = atomic_with_ghost!(
            &self.exc_locked.0 => store(false);
            ghost g =>
        {
            let tracked exc_guard = handle.get();
            self.inst.borrow().exc_release(cell_perms, cell_perms, &mut g, exc_guard);
        });
    }


    pub fn release_read(&self, read_handle: RwLockReadGuard<T>)
        requires
            self.wf(),
            self.wf_read_handle(&read_handle)
        ensures
            self.wf()
    {
        let RwLockReadGuard {tid, perms, handle } = read_handle;
        let res = atomic_with_ghost!(
            &self.ref_counts[tid].0 => fetch_sub(1);
            ghost g =>
        {
            let val = (tid as int, perms@);
            g = self.inst.borrow().shared_release(val, g, handle.get());
        });

    }

}

} // verus!
