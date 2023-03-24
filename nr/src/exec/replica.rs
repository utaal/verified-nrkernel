
use builtin_macros::verus_old_todo_no_ghost_blocks;

use crate::pervasive::prelude::*;
use crate::pervasive::cell::{PCell, PermissionOpt};
use crate::pervasive::map::Map;
use crate::pervasive::option::Option;
use crate::pervasive::vec::Vec;
use crate::pervasive::atomic_ghost::*;
use crate::pervasive::struct_with_invariants;




use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::types::*;
use crate::spec::unbounded_log::*;
use crate::spec::cyclicbuffer::*;


use super::log::NrLog;
use super::ThreadIdx;
use super::{LOG_SIZE, NUM_REPLICAS, MAX_THREADS_PER_REPLICA};
use super::rwlock::RwLock;
use super::cachepadded::CachePadded;
use super::context::Context;

use super::context::LogToken;

/// A token handed out to threads that replicas with replicas.
// #[derive(Copy, Clone, Eq, PartialEq)]
// pub struct ReplicaToken {
//     pub(crate) tid: ThreadIdx,
// }

pub type ReplicaToken = ThreadIdx;


verus_old_todo_no_ghost_blocks! {

struct_with_invariants!{
/// Ghost state that is protected by the combiner lock
///
///  - Dafny: glinear datatype CombinerLockState
///  - Rust:  N/A
pub struct CombinerLockStateGhost {
    pub taken: bool,

    // TODO
    // glinear flatCombiner: FCCombiner,
    pub combiner: Tracked<FlatCombiner::combiner>,

    /// Stores the token to access the op_buffer in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    pub op_buffer_token: Tracked<PermissionOpt<Vec<UpdateOp>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    pub responses_token: Tracked<PermissionOpt<Vec<ReturnType>>>,
}


pub closed spec fn inv(&self) -> bool {
    predicate {
        // if the lock is taken, then the combiner is collecting
        &&& self.taken ==> {
            &&& true
        }
        // if the lock is not taken, then the combiner is idling, here collecting with len 0
        &&& !self.taken ==> {
            &&& self.combiner@@.value.is_Collecting()
            &&& self.combiner@@.value.get_Collecting_0().len() == 0
        }
    }
}} // struct_with_invariants!


// impl CombinerLockStateGhost {
//     pub open spec fn is_taken(&self)  -> bool {
//         self.taken
//     }
// }

struct_with_invariants!{

/// An instance of a replicated data structure which uses a shared [`Log`] to
/// scale operations on the data structure across cores and processors.
///
///  - Dafny:   linear datatype Node
///  - Rust:    pub struct Replica<D>
#[repr(align(128))]
pub struct Replica {
    /// An identifier that we got from the Log when the replica was registered
    /// against the shared-log ([`Log::register()`]). Required to pass to the
    /// log when consuming operations from the log.
    ///
    ///  - Dafny: nodeId: uint64,
    ///  - Rust:  log_tkn: LogToken,
    pub log_tkn: LogToken,

    /// Stores the index of the thread currently doing flat combining. Field is
    /// zero if there isn't any thread actively performing flat-combining.
    /// Atomic since this acts as the combiner lock.
    ///
    ///  - Dafny: linear combiner_lock: CachePadded<Atomic<uint64, glOption<CombinerLockState>>>,
    ///  - Rust:  combiner: CachePadded<AtomicUsize>,
    pub combiner: CachePadded<AtomicU64<_, Option<CombinerLockStateGhost>, _>>,

    /// List of per-thread contexts. Threads buffer write operations here when
    /// they cannot perform flat combining (because another thread might already
    /// be doing so).
    ///
    ///  - Dafny: linear contexts: lseq<Context>,
    ///  - Rust:  contexts: Vec<Context<<D as Dispatch>::WriteOperation, <D as Dispatch>::Response>>,
    pub contexts: Vec<Context>,


    /// A buffer of operations for flat combining.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
    ///  - Rust:  buffer: RefCell<Vec<<D as Dispatch>::WriteOperation>>,
    pub op_buffer: PCell<Vec<UpdateOp>>,

    /// A buffer of results collected after flat combining. With the help of
    /// `inflight`, the combiner enqueues these results into the appropriate
    /// thread context.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear responses: LC.LinearCell<seq<nrifc.ReturnType>>,
    ///  - Rust:  result: RefCell<Vec<<D as Dispatch>::Response>>,
    pub responses: PCell<Vec<ReturnType>>,


    // The underlying data structure. This is shared among all threads that are
    // registered with this replica. Each replica maintains its own copy of
    // `data`.
    //
    //   - Dafny: linear replica: RwLock,
    //   - Rust:  data: CachePadded<RwLock<D>>,
    pub data: CachePadded<RwLock<DataStructureSpec>>,


    // /// Thread index that will be handed out to the next thread that registers
    // /// with the replica when calling [`Replica::register()`].
    // next: CachePadded<AtomicUsize>,
    // /// Number of operations collected by the combiner from each thread at any
    // inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

pub closed spec fn wf(&self) -> bool {

    // && (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int, nr.cb_loc_s))


    // invariant on the RwLock inner data structure
    // && replica.InternalInv()

    predicate {
        // && (forall i | 0 <= i < |contexts| :: i in contexts && contexts[i].WF(i, fc_loc))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> #[trigger] self.contexts[i as int].wf())
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> #[trigger] self.contexts[i as int].get_thread_id() == i)

        // && |contexts| == MAX_THREADS_PER_REPLICA as int
        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        // && 0 <= nodeId as int < NUM_REPLICAS as int
        &&& 0 <= self.log_tkn.id < NUM_REPLICAS
    }

    invariant on combiner specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost>) {
        &&& (v == 0) <==> g.is_Some()
        // && (forall v, g :: atomic_inv(combiner_lock.inner, v, g) <==> CombinerLockInv(v, g, fc_loc, ops, responses))
        &&& if v == 0 {
            &&& g.is_Some()  // the lock is not taken, the ghost state is Some
            &&& g.get_Some_0().inv()
            &&& g.get_Some_0().taken
            // &&& g.get_Some_0().combiner@@.instance == self.flat_combiner_instance
        } else {
            &&& g.is_None()  // the lock is taken, the ghost state is None
        }
    }
}

} // struct_with_invariants!


impl Replica  {

    /// Try to become acquire the combiner lock here. If this fails, then return None.
    ///
    ///  - Dafny: part of method try_combine
    #[inline(always)]
    fn acquire_combiner_lock(&self) -> (result: (bool, Tracked<Option<CombinerLockStateGhost>>))
        requires self.wf()
        ensures
            result.0 ==> result.1@.is_Some(),
            result.0 ==> result.1@.get_Some_0().combiner@@.value.is_Collecting(),
            result.0 ==> result.1@.get_Some_0().combiner@@.value.get_Collecting_0().len() == 0,
            // result.0 ==> self.combiner.0.ghost.is_None()
    {
        // OPT: try to check whether the lock is already present
        // for _ in 0..4 {
        //     if self.combiner.load(Ordering::Relaxed) != 0 { return None; }
        // }

        // XXX: we should pass in the replica token here, just setting the tid to 1 should work
        //      as the lock is basically a spinlock anyway
        let tid = 1u64;

        // Step 1: perform cmpxchg to acquire the combiner lock
        // if self.combiner.compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Acquire) != Ok(0) {
        //     None
        // } else {
        //     Some(CombinerLock { replica: self })
        // }

        let tracked lock_g: Option<CombinerLockStateGhost>;
        let res = atomic_with_ghost!(
            &self.combiner.0 => compare_exchange(0, tid + 1);
            update prev->next;
            ghost g => {
                if prev == 0 {
                    lock_g = tracked(g);    // obtain the protected lock statate
                    g = Option::None;       // we took the lock, set the ghost state to None,
                } else {
                    lock_g = tracked(None); // the lock was already taken, set it to None
                }
            }
        );

        if let Result::Ok(val) = res {
            (val == 0, tracked(lock_g))
        } else {
            (false, tracked(None))
        }
    }

    fn release_combiner_lock(&self, tracked lock_state: Tracked<CombinerLockStateGhost>)
        requires
            self.wf(),
            lock_state@.combiner@@.value.is_Collecting(),
            lock_state@.combiner@@.value.get_Collecting_0().len() == 0,
    {
        atomic_with_ghost!(
            &self.combiner.0 => store(0);
            update old_val -> new_val;
            ghost g
            => {
                assert(old_val != 0);
                assert(g.is_None());
                g = Some(lock_state.get());
            });
    }

    /// Appends an operation to the log and attempts to perform flat combining.
    /// Accepts a thread `tid` as an argument. Required to acquire the combiner lock.
    ///
    /// https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/nr/replica.rs#L788
    fn try_combine(&self, slog: &NrLog)
        requires
            self.wf(),
            slog.wf()
    {
        // Step 1: try to take the combiner lock to become combiner
        let (acquired, combiner_lock) = self.acquire_combiner_lock();

        // Step 2: if we are the combiner then perform flat combining, else return
        if acquired {
            assert(combiner_lock@.is_Some());
            // assert(self.combiner.0.load() != 0);
            let tracked mut combiner_lock = tracked(combiner_lock.get().tracked_unwrap());
            self.combine(slog, &mut combiner_lock);
            self.release_combiner_lock(combiner_lock);
        } else {
            // nothing to be done here.
        }
    }

    /// Performs one round of flat combining. Collects, appends and executes operations.
    ///
    /// https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/nr/replica.rs#L835
    fn combine(&self, slog: &NrLog, tracked combiner_lock: &mut Tracked<CombinerLockStateGhost>)
            // -> (result: Tracked<CombinerLockStateGhost>)
        requires
            self.wf(),
            slog.wf(),
            old(combiner_lock)@.combiner@@.value.is_Collecting(),
            old(combiner_lock)@.combiner@@.value.get_Collecting_0().len() == 0,
        ensures
            combiner_lock@.combiner@@.value.is_Collecting(),
            combiner_lock@.combiner@@.value.get_Collecting_0().len() == 0,

    {
        // Step 1: collect the operations from the threads
        // self.collect_thread_ops(&mut buffer, operations.as_mut_slice());



        // Step 2: Append all operations to the log

        // Step 3: Take the R/W lock on the data structure

        // Step 3: Execute all operations

        // Step 4: release the R/W lock on the data structure

        // Step 5: collect the results

        // combiner_lock
    }

    ///
    /// - Dafny: combine_collect()
    #[inline(always)]
    fn collect_thread_ops(&self, buffer: &mut Vec<UpdateOp>, operations: &mut [usize],
                            tracked flat_combiner:  Tracked<FlatCombiner::combiner>)
                            // -> (flat_combiner: Tracked<FlatCombiner::combiner>)
        requires
            self.wf(),
            // requires flatCombiner.loc_s == node.fc_loc
            self.flat_combiner_instance@ == flat_combiner@@.instance,
            // requires flatCombiner.state == FC.FCCombinerCollecting([])
            flat_combiner@@.value.is_Collecting(),
            flat_combiner@@.value.get_Collecting_0().len() == 0,
        ensures
            self.flat_combiner_instance@ == flat_combiner@@.instance,
            flat_combiner@@.value.is_Responding(),
            flat_combiner@@.value.get_Responding_1() == 0,

    {
        let tracked mut flat_combiner_mut = flat_combiner;


        // Collect operations from each thread registered with this replica.
        // let num_registered_threads = self.next.load(Ordering::Relaxed);
        // for i in 1..num_registered_threads {
        let n_contexts = self.contexts.len();
        let mut thread_idx = 0;
        while thread_idx < n_contexts {
            let res = atomic_with_ghost!(
                &self.contexts.index(0).atomic.0 => load();
                returning ret;
                ghost g // g : ContextGhost
            => {
                // nothing in the buffer here
                if ret == 0 {
                    self.flat_combiner_instance.borrow().combiner_collect_empty(&g.flat_combiner_slots, flat_combiner_mut.borrow_mut());
                } else {
                    g.flat_combiner_slots = self.flat_combiner_instance.borrow().combiner_collect_request(g.flat_combiner_slots, flat_combiner_mut.borrow_mut());
                }
            });

            thread_idx =  thread_idx + 1;
        }

        //     let ctxt_iter = self.contexts[i - 1].iter();
        //     operations[i - 1] = ctxt_iter.len();
        //     // meta-data is (), throw it away
        //     buffer.extend(ctxt_iter.map(|op| op.0));
        // }


        self.flat_combiner_instance.borrow().combiner_responding_start(flat_combiner_mut.borrow_mut());

        // (tracked(flat_combiner))
    }

    ///
    /// - Dafny: combine_respond
    fn distrubute_thread_resps(&self, buffer: &mut Vec<ReturnType>, operations: &mut [usize]) {
        // let (mut s, mut f) = (0, 0);
        // for i in 1..num_registered_threads {
        //     if operations[i - 1] == 0 {
        //         continue;
        //     };

        //     f += operations[i - 1];
        //     self.contexts[i - 1].enqueue_resps(&results[s..f]);
        //     s += operations[i - 1];
        //     operations[i - 1] = 0;
        // }
    }

    /// Registers a thread with this replica. Returns a [`ReplicaToken`] if the
    /// registration was successfull. None if the registration failed.
    pub fn register(&self) -> Option<ReplicaToken> {
        assert(false);
        None
    }

    /// Executes an immutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute(&self, slog: &NrLog, op: ReadonlyOp, idx: ReplicaToken) -> Result<ReturnType, () /* ReplicaError */>
        requires
            self.wf(),
            slog.wf(),
    {
        proof {
            // start the read transaction, get the ticket
            let tracked ticket = self.unbounded_log_instance.borrow().readonly_start(op);
        }

        // Step 1: Read the local tail value
        // let ctail = slog.get_ctail();

        // Step 2: wait until the replica is synced for reads, try to combine in mean time
        // while !slog.is_replica_synced_for_reads(&self.log_tkn, ctail) {
        //     if let Err(e) = self.try_combine(slog) {
        //         return Err((e, op));
        //     }
        //     spin_loop();
        // }

        // Step 3: Take the read-only lock, and read the value
        // let res = self.data.read(idx.tid() - 1).dispatch(op)


        // Step 4: Finish the read-only transaction, return result
        // self.unbounded_log_instance.readonly_finish(rid, op, res);

        assert(false);
        Err(())
    }

    /// Executes a mutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute_mut(&self, slog: &NrLog, op: UpdateOp, idx: ReplicaToken) -> Result<ReturnType, () /* ReplicaError */>
        requires
            slog.wf(),
            self.wf()
            // something about the idx
    {
        proof {
            let tracked ticket = self.unbounded_log_instance.borrow().update_start(op);
        }

        // Step 1: Enqueue the operation onto the thread local batch
        // while !self.make_pending(op.clone(), idx.tid()) {}

        // Step 2: Try to do flat combining to appy the update to the data structure
        // self.try_combine(slog)?;

        // Step 3: Obtain the result form the responses

        // Return the response to the caller function.
        // self.get_response(slog, idx.tid())
        assert(false);
        Err(())
    }

}


} // verus_old_todo_no_ghost_blocks! {