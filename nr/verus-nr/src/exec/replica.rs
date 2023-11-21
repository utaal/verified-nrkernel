#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;


use vstd::{
    prelude::*,
    map::Map,
    cell::{PCell, PointsTo, CellId},
    atomic_ghost::AtomicU64,
    atomic_with_ghost,
};

use crate::constants::{NUM_REPLICAS, MAX_REQUESTS, MAX_THREADS_PER_REPLICA, RESPONSE_CHECK_INTERVAL};

use crate::Dispatch;

// spec import
use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::cyclicbuffer::CyclicBuffer;
use crate::spec::types::{
    ReqId, NodeId,
};
#[cfg(verus_keep_ghost)] use crate::{
    is_readonly_stub, is_readonly_ticket, is_update_stub, is_update_ticket
};

// exec imports
use crate::exec::rwlock::RwLock;
use crate::exec::CachePadded;
use crate::exec::log::{NrLog, NrLogAppendExecDataGhost};
use crate::exec::context::{Context, PendingOperation, ThreadId, ThreadToken, FCClientRequestResponseGhost};
#[cfg(verus_keep_ghost)] use crate::exec::utils::{rids_match, rids_match_pop, rids_match_add_rid, rids_match_add_none};


verus! {

#[verifier(external_body)] /* vattr */
fn spin_loop_hint() {
    core::hint::spin_loop();
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replica Types
////////////////////////////////////////////////////////////////////////////////////////////////////


/// Unique identifier for the given replica (relative to the log)
pub type ReplicaId = usize;

/// a token that identifies the replica
///
// #[derive(Copy, Clone, Eq, PartialEq)]
pub struct ReplicaToken {
    pub /* REVIEW: (crate) */ rid: ReplicaId,
}

impl ReplicaToken {
    pub const fn new(rid: ReplicaId) -> (res: ReplicaToken)
        ensures res@ == rid
    {
        ReplicaToken { rid }
    }

    pub const fn clone(&self) -> (res: Self)
        ensures
            res == self
    {
        ReplicaToken { rid: self.rid }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.rid < NUM_REPLICAS
    }

    pub const fn id(&self) -> (result: ReplicaId)
        ensures result as nat == self.id_spec()
    {
        self.rid
    }

    pub open spec fn id_spec(&self) -> nat {
        self.rid as nat
    }

    pub open spec fn view(&self) -> nat {
        self.rid as nat
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replicated Data Structure
////////////////////////////////////////////////////////////////////////////////////////////////////

struct_with_invariants!{
/// Represents the data structure that is being replicated, protected by a RWLock
///
///  - Dafny: linear datatype NodeReplica = NodeReplica(
pub struct ReplicatedDataStructure<DT: Dispatch> {
    /// the actual data structure
    ///  - Dafny: linear actual_replica: nrifc.DataStructureType,
    pub data: DT,
    ///  - Dafny: glinear ghost_replica: Replica,
    pub replica: Tracked<UnboundedLog::replicas<DT>>,
    ///  - Dafny: glinear combiner: CombinerToken,
    pub combiner: Tracked<UnboundedLog::combiner<DT>>,
    ///  - Dafny: glinear cb: CBCombinerToken
    pub cb_combiner: Tracked<CyclicBuffer::combiner<DT>>
}

//  - Dafny: predicate WF(nodeId: nat, cb_loc_s: nat) {
pub open spec fn wf(&self, nid: NodeId, inst: UnboundedLog::Instance<DT>, cb: CyclicBuffer::Instance<DT>) -> bool {
    predicate {
        &&& self.combiner@@.instance == inst
        &&& self.replica@@.instance == inst

        &&& self.replica@@.value == self.data.view()
        &&& self.replica@@.key == nid
        &&& self.combiner@@.value.is_Ready()
        &&& self.combiner@@.key == nid
        &&& self.cb_combiner@@.key == nid
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.cb_combiner@@.instance == cb
    }
}} // struct_with_invariants


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replica
////////////////////////////////////////////////////////////////////////////////////////////////////


struct_with_invariants!{
/// An instance of a replicated data structure which uses a shared [`Log`] to
/// scale operations on the data structure across cores and processors.
///
///  - Dafny:   linear datatype Node
///  - Rust:    pub struct Replica<D>
#[repr(align(128))]
pub struct Replica<#[verifier::reject_recursive_types] DT: Dispatch> {
    /// An identifier that we got from the Log when the replica was registered
    /// against the shared-log ([`Log::register()`]). Required to pass to the
    /// log when consuming operations from the log.
    ///
    ///  - Dafny: nodeId: uint64,
    ///  - Rust:  log_tkn: LogToken,
    pub replica_token: ReplicaToken,

    /// Stores the index of the thread currently doing flat combining. Field is
    /// zero if there isn't any thread actively performing flat-combining.
    /// Atomic since this acts as the combiner lock.
    ///
    ///  - Dafny: linear combiner_lock: CachePadded<Atomic<uint64, glOption<CombinerLockState>>>,
    ///  - Rust:  combiner: CachePadded<AtomicUsize>,
    pub combiner: CachePadded<AtomicU64<_, Option<CombinerLockStateGhost<DT>>, _>>,

    /// List of per-thread contexts. Threads buffer write operations here when
    /// they cannot perform flat combining (because another thread might already
    /// be doing so).
    ///
    ///  - Dafny: linear contexts: lseq<Context>,
    ///  - Rust:  contexts: Vec<Context<<D as Dispatch>::WriteOperation, <D as Dispatch>::Response>>,
    pub contexts: Vec<Context<DT>>,

    /// A buffer of operations for flat combining.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
    ///  - Rust:  buffer: RefCell<Vec<<D as Dispatch>::WriteOperation>>,
    pub collected_operations: PCell<Vec<<DT as Dispatch>::WriteOperation>>,

    /// Number of operations collected by the combiner from each thread at any
    /// we just have one inflight operation per thread
    /// inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,
    pub collected_operations_per_thread: PCell<Vec<usize>>,

    /// A buffer of results collected after flat combining. With the help of
    /// `inflight`, the combiner enqueues these results into the appropriate
    /// thread context.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear responses: LC.LinearCell<seq<nrifc.ReturnType>>,
    ///  - Rust:  result: RefCell<Vec<<D as Dispatch>::Response>>,
    pub responses: PCell<Vec<<DT as Dispatch>::Response>>,

    /// The underlying data structure. This is shared among all threads that are
    /// registered with this replica. Each replica maintains its own copy of
    /// `data`.
    ///
    ///   - Dafny: linear replica: RwLock,
    ///   - Rust:  data: CachePadded<RwLock<D>>,
    pub data: CachePadded<RwLock<ReplicatedDataStructure<DT>>>,

    // Thread index that will be handed out to the next thread that registers
    // with the replica when calling [`Replica::register()`].
    // next: CachePadded<AtomicU64<_, FlatCombiner::num_threads, _>>,

    /// thread token that is handed out to the threads that register
    pub /* REVIEW: (crate) */ thread_tokens: Vec<ThreadToken<DT>>,

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

pub open spec fn wf(&self) -> bool {

    predicate {
        &&& (forall |i: int| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i]).wf(i as nat))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).flat_combiner_instance == self.flat_combiner_instance)
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).unbounded_log_instance == self.unbounded_log_instance)

        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        &&& 0 <= self.spec_id() < NUM_REPLICAS
        &&& self.data.0.wf()
        &&& (forall |v: ReplicatedDataStructure<DT>| #[trigger] self.data.0.inv(v) == v.wf(self.spec_id(), self.unbounded_log_instance@, self.cyclic_buffer_instance@))

        &&& self.flat_combiner_instance@.num_threads() == MAX_THREADS_PER_REPLICA
        &&& (forall |i| #![trigger self.thread_tokens[i]] 0 <= i < self.thread_tokens.len() ==> {
            self.thread_tokens[i].wf(self)
        })
    }

    invariant on combiner with (flat_combiner_instance, responses, collected_operations, collected_operations_per_thread) specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost<DT>>) {
        // v != 0 means lock is not taken, if it's not taken, the ghost state is Some
        &&& (v == 0) <==> g.is_some()
        //
        &&& (g.is_some() ==> g.get_Some_0().inv(flat_combiner_instance@, responses.id(), collected_operations.id(), collected_operations_per_thread.id()))
    }
}

} // struct_with_invariants!




impl<DT: Dispatch> Replica<DT> {
    pub fn new(replica_token: ReplicaToken, num_threads: usize, config: Tracked<ReplicaConfig<DT>>) -> (res: Self)
        requires
            num_threads == MAX_THREADS_PER_REPLICA,
            replica_token.id_spec() < NUM_REPLICAS,
            config@.wf(replica_token.id_spec())
        ensures
            res.wf(),
            res.spec_id() == replica_token.id_spec(),
            res.unbounded_log_instance@ == config@.unbounded_log_instance,
            res.cyclic_buffer_instance@ == config@.cyclic_buffer_instance,
    {
        let tracked ReplicaConfig {
            replica: replica,
            combiner: combiner,
            cb_combiner: cb_combiner,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = config.get();


        //
        // initialize the flat combiner
        //
        let tracked fc_instance:    FlatCombiner::Instance;
        let tracked mut fc_clients: Map<nat, FlatCombiner::clients>;
        let tracked mut fc_slots:   Map<nat, FlatCombiner::slots>;
        let tracked fc_combiner:    FlatCombiner::combiner;

        proof {
            let tracked (
                Tracked(fc_instance0), // FlatCombiner::Instance,
                Tracked(fc_clients0),  // Map<ThreadId, FlatCombiner::clients>,
                Tracked(fc_slots0),    // Map<ThreadId, FlatCombiner::slots>,
                Tracked(fc_combiner0), // FlatCombiner::combiner
            ) = FlatCombiner::Instance::initialize(num_threads as nat);
            fc_instance = fc_instance0;
            fc_clients = fc_clients0;
            fc_slots = fc_slots0;
            fc_combiner = fc_combiner0;
        }

        //
        // create the memory cells for the buffers
        //

        let (responses, responses_token) = PCell::new(Vec::with_capacity(num_threads));
        let (collected_operations, collected_operations_perm) = PCell::new(Vec::with_capacity(num_threads));
        let (collected_operations_per_thread, collected_operations_per_thread_perm) = PCell::new(Vec::with_capacity(num_threads));

        //
        // create the data structure protected by the RW lock
        //

        let replicated_data_structure = ReplicatedDataStructure {
            data: DT::init(),
            replica: Tracked(replica),
            combiner: Tracked(combiner),
            cb_combiner: Tracked(cb_combiner),
        };
        assert(replicated_data_structure.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance));
        // TODO: get the right spec function in there!
        let ghost data_structure_inv = |s: ReplicatedDataStructure<DT>| {
            s.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance)
        };
        let data = CachePadded(RwLock::new(replicated_data_structure, Ghost(data_structure_inv)));

        //
        // Create the thread contexts
        //
        let mut contexts : Vec<Context<DT>> = Vec::with_capacity(num_threads);
        let mut thread_tokens : Vec<ThreadToken<DT>> = Vec::with_capacity(num_threads);

        let mut idx = 0;
        while idx < num_threads
            invariant
                num_threads <= MAX_THREADS_PER_REPLICA,
                replica_token.id_spec() < NUM_REPLICAS,
                contexts.len() == idx,
                thread_tokens.len() == idx,
                0 <= idx <= num_threads,
                forall |i: nat| idx <= i < num_threads ==> fc_slots.contains_key(i),
                forall |i: nat| #![trigger fc_slots[i]] idx <= i < num_threads ==> {
                    &&& fc_slots[i]@.value.is_Empty()
                    &&& fc_slots[i]@.key == i
                    &&& fc_slots[i]@.instance == fc_instance
                },
                forall |i: nat| idx <= i < num_threads ==> fc_clients.contains_key(i),
                forall |i: nat| #![trigger fc_clients[i]] idx <= i < num_threads ==> {
                    &&& fc_clients[i]@.instance == fc_instance
                    &&& fc_clients[i]@.key == i
                    &&& fc_clients[i]@.value.is_Idle()
                },
                forall |i: nat| idx <= i < num_threads ==> fc_slots.contains_key(i),
                forall |i| #![trigger contexts[i]] 0 <= i < contexts.len() ==> {
                    &&& contexts[i].wf(i as nat)
                    &&& contexts[i].flat_combiner_instance == fc_instance
                    &&& contexts[i].unbounded_log_instance == unbounded_log_instance
                },
                forall |i| #![trigger thread_tokens[i]] 0 <= i < thread_tokens.len() ==> {
                    &&& thread_tokens[i].wf2()
                    &&& thread_tokens[i].thread_id_spec() == i
                    &&& thread_tokens[i].rid@ == replica_token.id_spec()
                    &&& thread_tokens[i].fc_client@@.instance == fc_instance
                    &&& thread_tokens[i].batch_perm@@.pcell == contexts[i].batch.0.id()
                }
        {
            let tracked slot;
            let tracked client;
            proof {
                slot = fc_slots.tracked_remove(idx as nat);
                client = fc_clients.tracked_remove(idx as nat);
            }
            let fc_inst = Tracked(fc_instance.clone());
            let ul_inst = Tracked(unbounded_log_instance.clone());

            let (context, batch_perm) = Context::new(idx, Tracked(slot), fc_inst, ul_inst);

            let token = ThreadToken {
                rid: replica_token.clone(),
                tid: idx as u32,
                fc_client: Tracked(client),
                batch_perm
            };

            contexts.push(context);
            thread_tokens.push(token);

            idx = idx + 1;
        }

        let tracked context_ghost = CombinerLockStateGhost {
            flat_combiner: Tracked(fc_combiner),
            collected_operations_perm,
            collected_operations_per_thread_perm,
            responses_token,
        };

        let tracked fc_inst = fc_instance.clone();
        let combiner = CachePadded(AtomicU64::new(Ghost((Tracked(fc_inst), responses, collected_operations, collected_operations_per_thread)), 0, Tracked(Option::Some(context_ghost))));

        //
        // Assemble the data struture
        //

        Replica {
            replica_token,
            combiner,
            contexts,
            collected_operations,
            collected_operations_per_thread,
            responses,
            data,
            thread_tokens,
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
            flat_combiner_instance: Tracked(fc_instance),
        }
    }

    pub fn id(&self) -> (res: ReplicaId)
        ensures res as nat == self.spec_id()
    {
        self.replica_token.id()
    }

    /// returns the replica id for this replica
    pub open spec fn spec_id(&self) -> NodeId {
        self.replica_token.id_spec()
    }

    /// Try to become acquire the combiner lock here. If this fails, then return None.
    ///
    ///  - Dafny: part of method try_combine
    #[inline(always)]
    fn acquire_combiner_lock(&self) -> (result: (bool, Tracked<Option<CombinerLockStateGhost<DT>>>))
        requires self.wf()
        ensures
          result.0 ==> result.1@.is_some(),
          result.0 ==> result.1@.get_Some_0().inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
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

        let tracked lock_g: Option<CombinerLockStateGhost<DT>>;
        let res = atomic_with_ghost!(
            &self.combiner.0 => compare_exchange(0, tid + 1);
            update prev->next;
            ghost g => {
                if prev == 0 {
                    lock_g = g;    // obtain the protected lock state
                    g = Option::None;       // we took the lock, set the ghost state to None,
                } else {
                    lock_g = Option::None; // the lock was already taken, set it to None
                }
            }
        );

        if let Result::Ok(val) = res {
            (val == 0, Tracked(lock_g))
        } else {
            (false, Tracked(Option::None))
        }
    }

    fn release_combiner_lock(&self, lock_state: Tracked<CombinerLockStateGhost<DT>>)
        requires
            self.wf(),
            lock_state@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
    {
        atomic_with_ghost!(
            &self.combiner.0 => store(0);
            update old_val -> new_val;
            ghost g
            => {
                g = Option::Some(lock_state.get());
            });
    }

    /// Appends an operation to the log and attempts to perform flat combining.
    /// Accepts a thread `tid` as an argument. Required to acquire the combiner lock.
    fn try_combine(&self, slog: &NrLog<DT>)
        requires
          self.wf(),
          slog.wf(),
          self.unbounded_log_instance@ == slog.unbounded_log_instance@,
          slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
    {
        // Step 1: try to take the combiner lock to become combiner
        let (acquired, combiner_lock) = self.acquire_combiner_lock();

        // Step 2: if we are the combiner then perform flat combining, else return
        if acquired {
            assert(combiner_lock@.is_some());
            let combiner_lock = Tracked(combiner_lock.get().tracked_unwrap());
            let combiner_lock = self.combine(slog, combiner_lock);
            self.release_combiner_lock(combiner_lock);
        } else {
            // nothing to be done here.
        }
    }

    /// Performs one round of flat combining. Collects, appends and executes operations.
    fn combine(&self, slog: &NrLog<DT>, combiner_lock: Tracked<CombinerLockStateGhost<DT>>)
            -> (result: Tracked<CombinerLockStateGhost<DT>>)
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            combiner_lock@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
        ensures
            result@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),

    {
        // disassemble the combiner lock
        let tracked combiner_lock = combiner_lock.get();
        let flat_combiner = Tracked(combiner_lock.flat_combiner.get());
        let tracked mut collected_operations_perm = combiner_lock.collected_operations_perm.get();
        let tracked mut collected_operations_per_thread_perm = combiner_lock.collected_operations_per_thread_perm.get();
        let tracked mut responses_token = combiner_lock.responses_token.get();

        // obtain access to the responses, operations and num_ops_per_thread buffers
        let mut responses = self.responses.take(Tracked(&mut responses_token));

        let mut operations = self.collected_operations.take(Tracked(&mut collected_operations_perm));

        // assert(self.collected_operations_per_thread.id() == collected_operations_per_thread_perm@.pcell);
        let mut num_ops_per_thread = self.collected_operations_per_thread.take(Tracked(&mut collected_operations_per_thread_perm));

        // Step 1: collect the operations from the threads
        // self.collect_thread_ops(&mut buffer, operations.as_mut_slice());
        let Tracked(collect_res) = self.collect_thread_ops(&mut operations, &mut num_ops_per_thread, flat_combiner);
        let tracked ThreadOpsData { flat_combiner, local_updates, request_ids, cell_permissions } = collect_res;

        // Step 2: Take the R/W lock on the data structure
        let (replicated_data_structure, write_handle) = self.data.0.acquire_write();
        let mut data = replicated_data_structure.data;
        let ghost_replica = replicated_data_structure.replica;
        let combiner = replicated_data_structure.combiner;
        let cb_combiner = replicated_data_structure.cb_combiner;

        // Step 3: Append all operations to the log
        let tracked append_exec_ghost_data = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids};
        let append_exec_ghost_data = slog.append(&self.replica_token, &operations, &mut responses, &mut data, Tracked(append_exec_ghost_data));


        // Step 3: Execute all operations
        let append_exec_ghost_data = slog.execute(&self.replica_token, &mut responses, &mut data, append_exec_ghost_data);
        let Tracked(append_exec_ghost_data) = append_exec_ghost_data;
        let tracked NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids } = append_exec_ghost_data;
        let tracked ghost_replica = ghost_replica.get();
        let tracked combiner = combiner.get();
        let tracked cb_combiner = cb_combiner.get();

        // Step 4: release the R/W lock on the data structure
        let replicated_data_structure = ReplicatedDataStructure  { data, replica: Tracked(ghost_replica), combiner: Tracked(combiner), cb_combiner: Tracked(cb_combiner) };
        self.data.0.release_write(replicated_data_structure, write_handle);

        // Step 5: collect the results
        let tracked thread_ops_data = ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions };
        let distribute_thread_resps_result = self.distribute_thread_resps(&mut responses, &mut num_ops_per_thread, Tracked(thread_ops_data));
        let tracked ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions } = distribute_thread_resps_result.get();

        // clear the buffers again
        responses.clear();
        operations.clear();
        num_ops_per_thread.clear();

        // // place the responses back into the state
        self.responses.put(Tracked(&mut responses_token), responses);
        self.collected_operations.put(Tracked(&mut collected_operations_perm), operations);
        self.collected_operations_per_thread.put(Tracked(&mut collected_operations_per_thread_perm), num_ops_per_thread);

        // re-assemble the combiner lock
        let tracked combiner_lock =  CombinerLockStateGhost { flat_combiner, collected_operations_perm: Tracked(collected_operations_perm), collected_operations_per_thread_perm: Tracked(collected_operations_per_thread_perm), responses_token: Tracked(responses_token) };
        Tracked(combiner_lock)
    }

    ///
    /// - Dafny: combine_collect()
    #[inline(always)]
    fn collect_thread_ops(&self, operations: &mut Vec<DT::WriteOperation>, num_ops_per_thread: &mut Vec<usize>,
                          flat_combiner:  Tracked<FlatCombiner::combiner>)
                             -> (response: Tracked<ThreadOpsData<DT>>)
        requires
            self.wf(),
            old(num_ops_per_thread).len() == 0,
            old(operations).len() == 0,
            flat_combiner@@.instance == self.flat_combiner_instance@,
            flat_combiner@@.value.is_Collecting(),
            flat_combiner@@.value.get_Collecting_0().len() == 0,
        ensures
            operations.len() <= MAX_REQUESTS,
            response@.collect_thread_ops_post(self.flat_combiner_instance, self.unbounded_log_instance@, num_ops_per_thread@, operations@, self.contexts@)
    {
        let mut flat_combiner = flat_combiner;

        let tracked mut updates: Map<nat, UnboundedLog::local_updates<DT>> = Map::tracked_empty();
        let tracked mut cell_permissions: Map<nat, PointsTo<PendingOperation<DT>>> = Map::tracked_empty();
        let ghost mut request_ids = Seq::empty();

        // let num_registered_threads = self.next.load(Ordering::Relaxed);
        let num_registered_threads = MAX_THREADS_PER_REPLICA;

        // Collect operations from each thread registered with this replica.
        // for i in 1..num_registered_threads {
        let mut thread_idx = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                self.wf(),
                operations.len() <= thread_idx,
                operations.len() == request_ids.len(),
                num_ops_per_thread.len() == thread_idx,
                self.contexts.len() == num_registered_threads,
                self.flat_combiner_instance@.num_threads() == num_registered_threads,
                flat_combiner@@.value.is_Collecting(),
                flat_combiner@@.value.get_Collecting_0().len() == thread_idx,
                flat_combiner@@.instance == self.flat_combiner_instance@,
                forall |i: nat| i < flat_combiner@@.value.get_Collecting_0().len() ==>
                    (num_ops_per_thread[i as int] > 0) ==
                    (#[trigger] flat_combiner@@.value.get_Collecting_0()[i as int]).is_some(),
                forall |i: nat| i < flat_combiner@@.value.get_Collecting_0().len() &&
                    (#[trigger] flat_combiner@@.value.get_Collecting_0()[i as int]).is_some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i]@.value.is_some()
                    },
                forall |i| 0 <= i < request_ids.len() <==> updates.contains_key(i),
                forall|i: nat| #![trigger updates[i]] i < request_ids.len() ==> {
                    &&& #[trigger] updates.contains_key(i)
                    &&& updates[i]@.instance == self.unbounded_log_instance
                    &&& updates[i]@.key == request_ids[i as int]
                    &&& updates[i]@.value.is_Init()
                    &&& updates[i]@.value.get_Init_op() == operations[i as int]
                },
                rids_match(flat_combiner@@.value.get_Collecting_0(), request_ids,
                    0, flat_combiner@@.value.get_Collecting_0().len(), 0, request_ids.len())

        {

            let tracked update_req : std::option::Option<UnboundedLog::local_updates<DT>>;
            let tracked batch_perms : std::option::Option<PointsTo<PendingOperation<DT>>>;
            let num_ops = atomic_with_ghost!(
                &self.contexts[thread_idx].atomic.0 => load();
                returning num_ops;
                ghost g // g : ContextGhost
            => {
                if num_ops == 1 {
                    self.flat_combiner_instance.borrow().pre_combiner_collect_request(&g.slots, flat_combiner.borrow());

                    rids_match_add_rid(flat_combiner.view().view().value.get_Collecting_0(), request_ids,
                        0, flat_combiner.view().view().value.get_Collecting_0().len(), 0, request_ids.len(),g.update.get_Some_0().view().key);

                    update_req = g.update;
                    batch_perms = g.batch_perms;

                    g.slots = self.flat_combiner_instance.borrow().combiner_collect_request(g.slots, flat_combiner.borrow_mut());
                    g.update = None;
                    g.batch_perms = None;
                } else {
                    rids_match_add_none(flat_combiner.view().view().value.get_Collecting_0(), request_ids,
                        0, flat_combiner.view().view().value.get_Collecting_0().len(), 0, request_ids.len());

                    self.flat_combiner_instance.borrow().combiner_collect_empty(&g.slots, flat_combiner.borrow_mut());
                    update_req = None;
                    batch_perms = None;
                }
            });

            if num_ops == 1 {
                let tracked batch_token_value = batch_perms.tracked_unwrap();
                let op = DT::clone_write_op(&self.contexts[thread_idx].batch.0.borrow(Tracked(&batch_token_value)).op);

                let tracked update_req = update_req.tracked_unwrap();
                proof {
                    updates.tracked_insert(request_ids.len() as nat, update_req);
                    cell_permissions.tracked_insert(thread_idx as nat, batch_token_value);
                }

                proof {
                    request_ids = request_ids.push(update_req@.key);
                }
                operations.push(op);
            }

            // set the number of active operations per thread
            num_ops_per_thread.push(num_ops as usize);
            thread_idx = thread_idx + 1;
        }

        proof {
            self.flat_combiner_instance.borrow().combiner_responding_start(flat_combiner.borrow_mut());
        }

        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner,
            request_ids: Ghost(request_ids),
            local_updates: Tracked(updates),
            cell_permissions: Tracked(cell_permissions)
        };
        Tracked(thread_ops_data)
    }


    /// - Dafny: combine_respond
    fn distribute_thread_resps(&self, responses: &mut Vec<DT::Response>, num_ops_per_thread: &mut Vec<usize>, thread_ops_data: Tracked<ThreadOpsData<DT>>)
        -> (res: Tracked<ThreadOpsData<DT>>)
        requires
            self.wf(),
            thread_ops_data@.distribute_thread_resps_pre(self.flat_combiner_instance, self.unbounded_log_instance@, old(num_ops_per_thread)@, old(responses)@, self.contexts@),
            rids_match(thread_ops_data@.flat_combiner@@.value.get_Responding_0(), thread_ops_data@.request_ids@,
                0, thread_ops_data@.flat_combiner@@.value.get_Responding_0().len(), 0, thread_ops_data@.request_ids@.len())
        ensures
            res@.distribute_thread_resps_post(self.flat_combiner_instance)

    {
        let tracked ThreadOpsData {
            flat_combiner: flat_combiner,
            request_ids: request_ids,
            local_updates: local_updates,
            cell_permissions: cell_permissions,
        } = thread_ops_data.get();
        let tracked mut flat_combiner = flat_combiner.get();
        let tracked mut cell_permissions = cell_permissions.get();
        let tracked mut updates = local_updates.get();


        // let num_registered_threads = self.next.load(Ordering::Relaxed);
        let num_registered_threads = MAX_THREADS_PER_REPLICA;

        // let (mut s, mut f) = (0, 0);
        // for i in 1..num_registered_threads {
        let mut thread_idx = 0;
        let mut resp_idx : usize = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                0 <= resp_idx <= responses.len(),
                resp_idx <= thread_idx,
                num_ops_per_thread.len() == num_registered_threads,
                request_ids@.len() == responses.len(),
                num_registered_threads == MAX_THREADS_PER_REPLICA,
                self.wf(),
                self.flat_combiner_instance@.num_threads() == num_registered_threads,
                flat_combiner@.instance == self.flat_combiner_instance@,
                flat_combiner@.value.is_Responding(),
                flat_combiner@.value.get_Responding_1() == thread_idx,
                flat_combiner@.value.get_Responding_0().len() == MAX_THREADS_PER_REPLICA,
                forall |i: nat| i < flat_combiner@.value.get_Responding_0().len() ==>
                    (num_ops_per_thread[i as int] > 0) ==
                    (#[trigger] flat_combiner@.value.get_Responding_0()[i as int]).is_some(),
                forall |i: nat| thread_idx <= i < flat_combiner@.value.get_Responding_0().len() &&
                    (#[trigger] flat_combiner@.value.get_Responding_0()[i as int]).is_some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i]@.value.is_some()
                    },
                forall|i: nat| resp_idx <= i < request_ids@.len() ==> {
                        &&& updates.contains_key(i)
                },
                forall|i: nat| #![trigger updates[i]] resp_idx <= i < request_ids@.len() ==> {
                    &&& updates.contains_key(i)
                    &&& updates[i]@.key == request_ids@[i as int]
                    &&& updates[i]@.value.is_Done()
                    &&& updates[i]@.instance == self.unbounded_log_instance@
                    &&& updates[i]@.value.get_Done_ret() == responses[i as int]
                },
                rids_match(flat_combiner@.value.get_Responding_0(), request_ids@,
                    thread_idx as nat, flat_combiner@.value.get_Responding_0().len(),
                    resp_idx as nat, request_ids@.len()),

        {

            proof {
                rids_match_pop(flat_combiner@.value.get_Responding_0(), request_ids@,
                    thread_idx as nat, flat_combiner@.value.get_Responding_0().len(),
                    resp_idx as nat, request_ids@.len());
            }

            let num_ops = num_ops_per_thread[thread_idx];

            // assert(flat_combiner@.value.get_Responding_1() < num_registered_threads);

            if num_ops == 0 {
                // if operations[i - 1] == 0 {
                //     continue;
                // };
                proof {
                    self.flat_combiner_instance.borrow().combiner_responding_empty(&mut flat_combiner);
                }

                // assert(forall|i: nat| #![trigger updates[i]] resp_idx <= i < request_ids@.len() ==> {
                //     &&& updates.contains_key(i)
                // });

            } else {
                //     f += operations[i - 1];
                //     self.contexts[i - 1].enqueue_resps(&results[s..f]);
                //     s += operations[i - 1];

                // obtain the element from the operation batch
                let tracked mut permission = cell_permissions.tracked_remove(thread_idx as nat);
                let mut op_resp = self.contexts[thread_idx].batch.0.take(Tracked(&mut permission));

                // update with the response
                let resp: DT::Response = DT::clone_response(&responses[resp_idx]);
                op_resp.resp = Some(resp);

                // place the element back into the batch
                self.contexts[thread_idx].batch.0.put(Tracked(&mut permission), op_resp);

                //     operations[i - 1] = 0;
                atomic_with_ghost!(
                    &self.contexts[thread_idx].atomic.0 => store(0);
                    update prev -> next;
                    ghost g // g : ContextGhost
                    => {
                        // record the pre-states of the transition values
                        g.slots = self.flat_combiner_instance.borrow().combiner_responding_result(g.slots, &mut flat_combiner);
                        g.batch_perms = Some(permission);
                        g.update = Some(updates.tracked_remove(resp_idx as nat));
                    }
                );
                resp_idx = resp_idx + 1;
            }
            thread_idx = thread_idx + 1;
        }

        proof {
            self.flat_combiner_instance.borrow().combiner_responding_done(&mut flat_combiner);
        }

        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner: Tracked(flat_combiner),
            request_ids,
            local_updates: Tracked(updates),
            cell_permissions : Tracked(cell_permissions),
        };

        Tracked(thread_ops_data)
    }

    /// Registers a thread with this replica. Returns a [`ReplicaToken`] if the
    /// registration was successfull. None if the registration failed.
    pub fn register(&mut self) -> (res: Option<ThreadToken<DT>>)
        requires old(self).wf()
        ensures self.wf(),
        old(self).replica_token@ == self.replica_token@,
        old(self).unbounded_log_instance@ == self.unbounded_log_instance@,
        old(self).cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
        res.is_Some() ==> res.get_Some_0().wf(self)
    {
        self.thread_tokens.pop()
    }

    #[verifier(external_body)] /* vattr */
    pub fn progress(line: u32) {
        println!("Replica:: progress {line}");
    }

    /// Executes an immutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute(&self, slog: &NrLog<DT>, op: DT::ReadOperation, tkn: ThreadToken<DT>, ticket: Tracked<UnboundedLog::local_reads<DT>>)
        -> (result: (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            slog.wf(),
            tkn.wf(self),
            tkn.batch_perm@@.pcell == self.contexts[tkn.thread_id_spec() as int].batch.0.id(),
            self.replica_token@ == tkn.replica_token()@,
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@,
            is_readonly_ticket(ticket@, op, slog.unbounded_log_instance@)
        ensures
            result.1.wf(&self),
            result.1.batch_perm@@.pcell == self.contexts[result.1.thread_id_spec() as int].batch.0.id(),
            is_readonly_stub(result.2@, ticket@@.key, result.0, slog.unbounded_log_instance@)
    {
        // let tracked local_reads : UnboundedLog::local_reads<DT>;
        // proof {
        //     let tracked ticket = self.unbounded_log_instance.borrow().readonly_start(op);
        //     local_reads = ticket.1.get();
        // }
        let ghost rid : nat = ticket@@.key;
        proof {
            rid = ticket@@.key;
        }
        let ghost nid = tkn.replica_id_spec();

        // Step 1: Read the local tail value
        // let ctail = slog.get_ctail();
        let (version_upper_bound, ticket) = slog.get_version_upper_bound(ticket);

        // Step 2: wait until the replica is synced for reads, try to combine in mean time
        // while !slog.is_replica_synced_for_reads(&self.log_tkn, ctail) {
        //     if let Err(e) = self.try_combine(slog) {
        //         return Err((e, op));
        //     }
        //     spin_loop();
        // }
        let (mut is_synced, mut ticket) = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, ticket);
        while !is_synced
            invariant
                self.wf(),
                slog.wf(),
                !is_synced ==> ticket@@.value.is_VersionUpperBound(),
                !is_synced ==> ticket@@.value.get_VersionUpperBound_version_upper_bound() == version_upper_bound,
                !is_synced ==> ticket@@.value.get_VersionUpperBound_op() == op,
                is_synced ==> ticket@@.value.is_ReadyToRead(),
                is_synced ==> ticket@@.value.get_ReadyToRead_node_id() == self.spec_id(),
                is_synced ==> ticket@@.value.get_ReadyToRead_op() == op,
                ticket@@.instance == self.unbounded_log_instance@,
                ticket@@.key == rid,
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
        {
            self.try_combine(slog);
            spin_loop_hint();
            let res = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, ticket);
            is_synced = res.0;
            ticket = res.1;
        }

        let tracked ticket = ticket.get();

        // Step 3: Take the read-only lock, and read the value
        // let res = self.data.read(idx.tid() - 1).dispatch(op)
        let read_handle = self.data.0.acquire_read();
        let replica = self.data.0.borrow(&read_handle);
        let result = replica.data.dispatch(op);

        let tracked ticket = self.unbounded_log_instance.borrow().readonly_apply(rid, replica.replica.borrow(), ticket, replica.combiner.borrow());
        self.data.0.release_read(read_handle);

        // // Step 4: Finish the read-only transaction, return result
        // let tracked local_reads = local_reads;
        // proof {
        //     self.unbounded_log_instance.borrow().readonly_finish(rid, op, result, local_reads);
        // }

        // assert(false);
        (result, tkn, Tracked(ticket))
    }

    /// Executes a mutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute_mut(&self, slog: &NrLog<DT>, op: DT::WriteOperation, tkn: ThreadToken<DT>, ticket: Tracked<UnboundedLog::local_updates<DT>>)
            -> (result: (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>))
        requires
            slog.wf(),
            self.wf(),
            tkn.wf(self),
            tkn.batch_perm@@.pcell == self.contexts[tkn.thread_id_spec() as int].batch.0.id(),
            self.replica_token == tkn.replica_token(),
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@,
            is_update_ticket(ticket@, op, slog.unbounded_log_instance@)
        ensures
            result.1.wf(self),
            result.1.batch_perm@@.pcell == self.contexts[result.1.thread_id_spec() as int].batch.0.id(),
            is_update_stub(result.2@, ticket@@.key, result.0, slog.unbounded_log_instance@)
    {

        let tracked ticket = ticket.get();

        let ghost req_id : nat = ticket@.key;

        let ThreadToken { rid, tid, fc_client, batch_perm } = tkn;

        // Step 1: Enqueue the operation onto the thread local batch
        // while !self.make_pending(op.clone(), idx.tid()) {}
        // Note: if we have the thread token, this will always succeed.
        let tracked context_ghost = FCClientRequestResponseGhost { batch_perms: Some(batch_perm.get()), cell_id: Ghost(self.contexts[tkn.thread_id_spec() as int].batch.0.id()), local_updates: Some(ticket), fc_clients: fc_client.get() };

        let mk_pending_res = self.make_pending(op, tid, Tracked(context_ghost));
        let context_ghost = mk_pending_res.1;

        // Step 2: Try to do flat combining to appy the update to the data structure
        self.try_combine(slog);

        // Step 3: Obtain the result form the responses
        let response = self.get_response(slog, tid, Ghost(req_id), context_ghost);
        let context_ghost = response.1;

        let tracked FCClientRequestResponseGhost { batch_perms: batch_perms, cell_id, local_updates: ticket, fc_clients: fc_clients } = context_ghost.get();
        let tracked ticket = ticket.tracked_unwrap();


        let tracked batch_perm = batch_perms.tracked_unwrap();

        (
            response.0,
            ThreadToken { rid, tid, fc_client: Tracked(fc_clients), batch_perm: Tracked(batch_perm) },
            Tracked(ticket)
        )
    }

    /// Enqueues an operation inside a thread local context. Returns a boolean
    /// indicating whether the operation was enqueued (true) or not (false).
    fn make_pending(&self, op: DT::WriteOperation, tid: ThreadId, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
     -> (res: (bool, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            self.wf(),
            0 <= tid < self.contexts.len(),
            context_ghost@.enqueue_op_pre(tid as nat, op, self.contexts[tid as int].batch.0.id(), self.flat_combiner_instance@, self.unbounded_log_instance@)
        ensures
            res.1@.enqueue_op_post(context_ghost@)
    {
        let context = &self.contexts[tid as usize];
        context.enqueue_op(op, context_ghost)
    }

    /// Busy waits until a response is available within the thread's context.
    fn get_response(&self, slog: &NrLog<DT>, tid: ThreadId, req_id: Ghost<ReqId>, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
        -> (res: (DT::Response, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            0 <= tid < self.contexts.len(),
            context_ghost@.dequeue_resp_pre(self.contexts[tid as int].batch.0.id(), tid as nat, self.flat_combiner_instance@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, Some(res.0), self.unbounded_log_instance@),
    {
        let mut context_ghost_new = context_ghost;
        let context = &self.contexts[tid as usize];

        let mut iter : usize = 0;
        let mut r = None;
        while r.is_none()
            invariant
                slog.wf(),
                self.wf(),
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
                context.wf(tid as nat),
                context.flat_combiner_instance@ == self.flat_combiner_instance@,
                context.unbounded_log_instance@ == self.unbounded_log_instance@,
                0 <= iter <= RESPONSE_CHECK_INTERVAL,
                r.is_None() ==> context_ghost_new@.dequeue_resp_pre(context.batch.0.id(), tid as nat, self.flat_combiner_instance@),
                context_ghost_new@.dequeue_resp_post(context_ghost@, r, self.unbounded_log_instance@)
        {
            if iter == RESPONSE_CHECK_INTERVAL {
                self.try_combine(slog);
                iter = 0;
            }

            let deq_resp_result = context.dequeue_response(context_ghost_new);
            r = deq_resp_result.0;
            context_ghost_new = deq_resp_result.1;

            iter = iter + 1;
        }

        let r = r.unwrap();
        (r, context_ghost_new)
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost Structures
////////////////////////////////////////////////////////////////////////////////////////////////////

/// struct containing arguments for creating a new replica
pub tracked struct ReplicaConfig<DT: Dispatch> {
    pub tracked replica: UnboundedLog::replicas<DT>,
    pub tracked combiner: UnboundedLog::combiner<DT>,
    pub tracked cb_combiner: CyclicBuffer::combiner<DT>,
    pub tracked unbounded_log_instance: UnboundedLog::Instance<DT>,
    pub tracked cyclic_buffer_instance: CyclicBuffer::Instance<DT>,
}

impl<DT: Dispatch> ReplicaConfig<DT> {
    pub open spec fn wf(&self, nid: nat) -> bool {
        &&& self.combiner@.instance == self.unbounded_log_instance
        &&& self.cb_combiner@.instance == self.cyclic_buffer_instance

        &&& self.replica@.value == DT::init_spec()
        &&& self.replica@.key == nid
        &&& self.replica@.instance == self.unbounded_log_instance
        &&& self.combiner@.value.is_Ready()
        &&& self.combiner@.key == nid
        &&& self.cb_combiner@.key == nid
        &&& self.cb_combiner@.value.is_Idle()
        &&& self.cb_combiner@.instance == self.cyclic_buffer_instance
    }
}


struct_with_invariants!{
/// Ghost state that is protected by the combiner lock
///
///  - Dafny: glinear datatype CombinerLockState
///  - Rust:  N/A
pub tracked struct CombinerLockStateGhost<DT: Dispatch> {
    // glinear flatCombiner: FCCombiner,
    pub flat_combiner: Tracked<FlatCombiner::combiner>,

    /// Stores the token to access the collected_operations in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    pub collected_operations_perm: Tracked<PointsTo<Vec<<DT as Dispatch>::WriteOperation>>>,

    /// Stores the token to access the number of collected operations in the replica
    pub collected_operations_per_thread_perm: Tracked<PointsTo<Vec<usize>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    pub responses_token: Tracked<PointsTo<Vec<<DT as Dispatch>::Response>>>,
}

//  - Dafny: predicate CombinerLockInv(v: uint64, g: glOption<CombinerLockState>, fc_loc: nat,
//                                     ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
//                                     responses: LC.LinearCell<seq<nrifc.ReturnType>>)
//
// Note: this predicate only holds when the lock is not taken.
pub open spec fn inv(&self, combiner_instance: FlatCombiner::Instance, responses_id: CellId, op_buffer_id: CellId, thread_ops: CellId) -> bool {
    predicate {
        &&& self.flat_combiner@@.value.is_Collecting()
        &&& self.flat_combiner@@.value.get_Collecting_0().len() == 0
        &&& self.flat_combiner@@.instance == combiner_instance

        &&& self.collected_operations_perm@@.value.is_some()
        &&& self.collected_operations_perm@@.pcell == op_buffer_id
        &&& self.collected_operations_perm@@.value.get_Some_0().len() == 0 // we use vector push MAX_THREADS_PER_REPLICA

        &&& self.responses_token@@.value.is_some()
        &&& self.responses_token@@.pcell == responses_id
        &&& self.responses_token@@.value.get_Some_0().len() == 0 // we use vector push MAX_THREADS_PER_REPLICA

        &&& self.collected_operations_per_thread_perm@@.value.is_some()
        &&& self.collected_operations_per_thread_perm@@.pcell == thread_ops
        &&& self.collected_operations_per_thread_perm@@.value.get_Some_0().len() == 0
    }
}} // struct_with_invariants!



tracked struct ThreadOpsData<DT: Dispatch> {
    flat_combiner: Tracked<FlatCombiner::combiner>,
    request_ids: Ghost<Seq<ReqId>>,
    local_updates: Tracked<Map<nat, UnboundedLog::local_updates<DT>>>,
    cell_permissions: Tracked<Map<nat, PointsTo<PendingOperation<DT>>>>,
}

impl<DT: Dispatch> ThreadOpsData<DT> {
    spec fn shared_inv(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>, num_ops_per_thread: Seq<usize>,
                       replica_contexts: Seq<Context<DT>>) -> bool {
        &&& self.flat_combiner@@.instance == flat_combiner_instance@
        &&& self.flat_combiner@@.value.is_Responding()
        &&& self.flat_combiner@@.value.get_Responding_0().len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& num_ops_per_thread.len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& self.flat_combiner@@.value.get_Responding_1() == 0

        &&& (forall|i: nat|
           #![trigger num_ops_per_thread[i as int]]
           #![trigger self.flat_combiner@@.value.get_Responding_0()[i as int]]
            i < self.flat_combiner@@.value.get_Responding_0().len() ==> {
            &&& (num_ops_per_thread[i as int] > 0) == self.flat_combiner@@.value.get_Responding_0()[i as int].is_some()
            &&& self.flat_combiner@@.value.get_Responding_0()[i as int].is_some() ==> {
                &&& self.cell_permissions@.contains_key(i)
                &&& self.cell_permissions@[i]@.pcell === replica_contexts[i as int].batch.0.id()
                &&& self.cell_permissions@[i]@.value.is_some()
            }
        })

    }

    spec fn distribute_thread_resps_pre(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>,
                                        unbounded_log_instance: UnboundedLog::Instance<DT>,
                                        num_ops_per_thread: Seq<usize>, responses: Seq<DT::Response>,
                                        replica_contexts: Seq<Context<DT>>) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)

        &&& self.request_ids@.len() == responses.len()
        &&& (forall |i| 0 <= i < self.request_ids@.len() ==> self.local_updates@.contains_key(i))
        &&& (forall|i: nat| #![trigger self.local_updates@[i]] i < self.request_ids@.len() ==> {
            &&& self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.instance == unbounded_log_instance
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Done()
            &&& self.local_updates@[i]@.value.get_Done_ret() == responses[i as int]
        })

        &&& rids_match(self.flat_combiner@@.value.get_Responding_0(), self.request_ids@,
                 0, self.flat_combiner@@.value.get_Responding_0().len(), 0, self.request_ids@.len())
    }

    spec fn distribute_thread_resps_post(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>) -> bool
    {
        &&& self.flat_combiner@@.instance == flat_combiner_instance@
        &&& self.flat_combiner@@.value.is_Collecting()
        &&& self.flat_combiner@@.value.get_Collecting_0().len() == 0
    }

    spec fn collect_thread_ops_post(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>,
                unbounded_log_instance: UnboundedLog::Instance<DT>, num_ops_per_thread: Seq<usize>,
                operations: Seq<DT::WriteOperation>, replica_contexts: Seq<Context<DT>>) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)
        &&& self.request_ids@.len() == operations.len()
        &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
        &&& (forall|i: nat| #![trigger self.local_updates@[i]] i < self.request_ids@.len() ==> {
            &&& #[trigger] self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.instance == unbounded_log_instance
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Init()
            &&& self.local_updates@[i]@.value.get_Init_op() == operations[i as int]
        })

        &&& rids_match(self.flat_combiner@@.value.get_Responding_0(), self.request_ids@,
                 0, self.flat_combiner@@.value.get_Responding_0().len(), 0, self.request_ids@.len())
    }
}

} // verus!
