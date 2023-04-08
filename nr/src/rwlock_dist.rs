#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

mod pervasive;
mod spec;

use crate::pervasive::*;
use crate::pervasive::vec::*;
use crate::pervasive::modes::*;
use crate::pervasive::multiset::*;
use crate::pervasive::map::*;
use crate::pervasive::seq::*;
use crate::pervasive::option::*;
use crate::pervasive::atomic_ghost::*;
use crate::pervasive::cell::{PCell, PointsTo};
use crate::pervasive::result::Result;
use state_machines_macros::tokenized_state_machine;

use spec::rwlock::*;

verus!{

/// a simpe cache padding for the struct fields
#[repr(align(128))]
pub struct CachePadded<T>(pub T);

#[verifier(external_body)] /* vattr */
pub fn spin_loop_hint() {
    core::hint::spin_loop();
}


////////////////////////////////////////////////////////////////////////////////////////////////////
//  The Reader / Shared Guard of the RwLock
////////////////////////////////////////////////////////////////////////////////////////////////////




struct_with_invariants!{


///  structure used to release the exclusive write access of a lock
///
/// An ExclusiveGuard is a special ghost object you get when you call `acquire` on a RwLock. Its
/// only purpose is that it allows you to call `release` again later. This requirement allows us
/// to enforce that no client calls a `release` without previously calling `acquire`.
///
/// TODO: implement drop?
tracked struct RwLockWriteGuard<T> {
    // glinear exc_obtained_token: Token,
    pub t_exc_guard: DistRwLock::exc_guard<T>,
    pub t_data_perm: T,
    // glinear empty_cell_contents: HandleTypeMod.Handle,
    pub g_rw_lock : DistRwLock::Instance<T>,
}

pub open spec fn inv(&self, expected_lock: DistRwLock::Instance<T>) -> bool {
    predicate {
        // && exc_obtained_token.loc == m.loc
        self.t_exc_guard@.instance == expected_lock
        // && IsExcAcqObtained(exc_obtained_token.val)

        // && empty_cell_contents.lcell == m.lcell.inner // empty_cell_contents is talking about m's cell
        // && empty_cell_contents.v.None?  // m.cell is empty, ready to be give-n back a value at release time.


        //&& m == expected_lock
        &&& self.g_rw_lock == expected_lock
    }
}

} // struct_with_invariants!


////////////////////////////////////////////////////////////////////////////////////////////////////
//  The Writer / Exclusive Guard of the RwLock
////////////////////////////////////////////////////////////////////////////////////////////////////

type ThreadId = u32;

struct_with_invariants!{

/// Structure used to release the shared read access of a lock
///
/// A SharedGuard is for shared access. Use the `borrow_shared` method below to obtain shared access
/// to the data structure stored in the mutex.
///
/// TODO: implement drop?
struct RwLockReadGuard<T>{
    /// Thread ID of the thread that acquired the shared lock
    ///
    /// The shared access can be released on a different thread than the one that acquired it;
    /// the guard carries with it the necessary non-ghost thread id that matches the thread_id
    /// associated with the ghost shared_obtained_token.
    pub acquiring_thread_id: ThreadId,

    // glinear shared_obtained_token: Token,

    pub ghost rw_lock : DistRwLock::Instance<T>,
    pub ghost value: T,
}

pub open spec fn inv(&self, expected_lock: DistRwLock::Instance<T>) -> bool {
    predicate {
        &&& 0 <= (self.acquiring_thread_id as nat) < self.rw_lock.rc_width()

        // && shared_obtained_token.loc == m.loc
        // && shared_obtained_token.val.M?
        // && shared_obtained_token.val == RwLockMod.SharedAcqHandle(RwLockMod.SharedAcqObtained(
        //   acquiring_thread_id as nat, StoredContents()))
        &&& self.rw_lock == expected_lock
    }
}

} // struct_with_invariants!



struct_with_invariants!{
struct RwLock<T> {
    /// the exclusive flag
    pub(crate) exc_locked: CachePadded<AtomicBool<_, DistRwLock::exc_locked<T>, _>>,
    /// reference counts
    pub(crate) ref_counts: Vec<CachePadded<AtomicU64<_, DistRwLock::ref_counts<T>, _>>>,

    /// the instance of the lock
    pub tracked inst: DistRwLock::Instance<T>,
}

pub open spec fn wf(&self) -> bool {

    predicate {
        // && |refCounts| == RC_WIDTH
        &&& self.inst.rc_width() == self.ref_counts@.len()

        &&& forall |i: int| (0 <= i && i < self.ref_counts@.len()) ==>
            (#[trigger] self.ref_counts@.index(i)).0.well_formed()
            && self.ref_counts@.index(i).0.constant() === (self.inst, i)
    }

    invariant on exc_locked with (inst) specifically (self.exc_locked.0) is (b: bool, g: DistRwLock::exc_locked<T>) {
        g@ === DistRwLock::token![ inst => exc_locked => b ]
    }

    invariant on ref_counts with (inst)
        forall |i: int|
        where (0 <= i < self.ref_counts@.len())
        specifically (self.ref_counts@[i].0)
        is (v: u64, g: DistRwLock::ref_counts<T>)
    {
        g@ === DistRwLock::token![ inst => ref_counts => i => v as int ]
    }
}

} // struct_with_invariants!

impl<T> RwLock<T> {
    #[verifier(spinoff_prover)]
    fn new(rc_width: usize, t: T) -> (res: Self)
        requires 0 < rc_width
        ensures res.wf()
    {
        let tracked inst;
        let tracked exc_locked_token;
        let tracked mut ref_counts_tokens;
        proof {
            let tracked (Trk(inst0), Trk(exc_locked_token0), Trk(ref_counts_tokens0), _, _, _, _) =
                DistRwLock::Instance::initialize(rc_width as int, t, Option::Some(t));
            inst = inst0;
            exc_locked_token = exc_locked_token0;
            ref_counts_tokens = ref_counts_tokens0;
        }

        let exc_locked_atomic = AtomicBool::new(inst, false, exc_locked_token);

        let mut v: Vec<CachePadded<AtomicU64<(DistRwLock::Instance<T>, int), DistRwLock::ref_counts<T>, _>>>
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
                forall(|j: int| 0 <= j && j < i ==>
                    (#[trigger]v@.index(j)).0.well_formed()
                      && equal(v@.index(j).0.constant(), (inst, j))
                ),
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

            let tracked ref_count_token;
            proof {
                ref_count_token = ref_counts_tokens.tracked_remove(i as int);
            }

            let rc_atomic = AtomicU64::new((inst, spec_cast_integer::<_, int>(i)), 0, ref_count_token);
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
            exc_locked: CachePadded(exc_locked_atomic),
            ref_counts: v,
            inst: inst,
        };

        assert(s.inst.rc_width() == s.ref_counts@.len());

        s
    }


    pub fn acquire_exclusive(&self) -> (res: Tracked<RwLockWriteGuard<T>>)
        requires
            self.wf(),
            // internal inv
            //
        ensures
            res@.inv(self.inst)
    {
        let tracked mut t_exc_pending : Option<DistRwLock::exc_pending<T>> = Option::None;

        let mut got_exc = false;
        while !got_exc
            invariant
                self.wf(),
                got_exc ==> t_exc_pending.is_Some() && t_exc_pending.get_Some_0()@.instance == self.inst && t_exc_pending.get_Some_0()@.value == 0
        {
            let locked = atomic_with_ghost!(
                &self.exc_locked.0 => compare_exchange(false, true);
                update prev -> next;
                ghost g => {
                    if prev == false {
                        // lock taken
                        t_exc_pending = Option::Some(self.inst.exc_start(&mut g));
                    }
                }
            );

            got_exc = if let Result::Ok(_) = locked {
                true
            } else {
                false
            };
        }

        let tracked mut t_exc_pending = t_exc_pending.tracked_unwrap();

        assert(self.ref_counts.len() == self.inst.rc_width());

        let mut visited = 0;
        let rc_width = self.ref_counts.len();
        while visited < rc_width
            invariant
                self.wf(),
                0 <= visited <= rc_width,
                rc_width == self.inst.rc_width(),
                t_exc_pending@.instance == self.inst,
                t_exc_pending@.value == visited,

        {
            let ref_count = atomic_with_ghost!(
                &self.ref_counts.index(visited).0 => load();
                returning ref_count;
                ghost g => {
                    if ref_count == 0 {
                        // there are no outstanding shared references, we can advance
                        t_exc_pending = self.inst.exc_check_count(&g, t_exc_pending);
                    }
                }
            );

            if ref_count == 0 {
                visited = visited + 1;
            } else {
                spin_loop_hint();
            }
        }

        // finish: update the guard
        let tracked (t_data_perm, t_exc_guard) =  self.inst.exc_finish(t_exc_pending);

        let tracked guard = RwLockWriteGuard {
            t_exc_guard: t_exc_guard.0,
            t_data_perm: t_data_perm.0,
            g_rw_lock: self.inst.clone(),
        };

       tracked(guard)
    }

    pub fn release_exclusive(&self, guard: Tracked<RwLockWriteGuard<T>>)
        requires
            self.wf(),
            guard@.inv(self.inst)
    {
        let tracked RwLockWriteGuard { t_exc_guard, t_data_perm, g_rw_lock } = guard.get();

        atomic_with_ghost!(
            &self.exc_locked.0 => store(false);
            ghost g => {
                self.inst.exc_release(t_data_perm, t_data_perm, &mut g, t_exc_guard);
            }
        );
    }

    pub fn acquire_shared(&self, tid: ThreadId)
        requires
            self.wf(),
            0 <= tid < self.ref_counts.len()
    {
        // let tracked shared_handle = Option::None;
        while true
            invariant
                self.wf(),
                0 <= tid < self.ref_counts.len()
        {

            // Spin loop until nobody has the exclusive access acquired.
            // Note we don't do anything with handles here, because correctness
            // doesn't (can't!) depend on the value we observe for the
            // exclusiveFlag here.
            let mut exc_acquired = atomic_with_ghost!(
                &self.exc_locked.0 => load();
                returning locked;
                ghost g => { }
            );

            while exc_acquired
                invariant
                    self.wf(),
                    0 <= tid < self.ref_counts.len(),
            {
                spin_loop_hint();
                let locked = atomic_with_ghost!(
                    &self.exc_locked.0 => load();
                    returning locked;
                    ghost g => { }
                );
            }

            // Increment my thread-specific refcount to indicate my enthusiasm to get this shared access.
            atomic_with_ghost!(
                &self.ref_counts.index(tid as usize).0 => fetch_add(1);
                returning locked;
                ghost g => {
                    self.inst.shared_start(tid)

                }
            );

        }
    }

    pub fn release_shared(&self) {

    }
}


} // struct_with_invariants!

pub fn main() {}