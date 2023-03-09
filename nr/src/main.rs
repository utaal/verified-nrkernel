// the verus dependencies
#[macro_use]
mod pervasive;
use pervasive::prelude::*;

use pervasive::map::Map;
use pervasive::vec::Vec;
use pervasive::cell::{PCell, PermissionOpt};
use pervasive::option::Option;
mod spec;
// mod exec;

use spec::types::*;
use spec::unbounded_log::UnboundedLog;
use spec::cyclicbuffer::CyclicBuffer;

use pervasive::atomic_ghost::*;

use crate::pervasive::struct_with_invariants;


/// a simpe cache padding for the struct fields
#[repr(align(128))]
pub struct CachePadded<T>(T);


/// Unique identifier for the given replicas (e.g., its NUMA node)
pub type ReplicaId = usize;

/// A (monotoically increasing) number that uniquely identifies a thread that's
/// registered with the replica.
pub type ThreadIdx = usize;

/// the maximum number of replicas
pub const MAX_REPLICAS_PER_LOG: usize = 16;

/// the number of replicas we have
pub const NUM_REPLICAS: usize = 4;

/// the size of the log in bytes
pub const DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;

pub const LOG_SIZE: usize = 1024;

/// maximum number of threads per replica
pub const MAX_THREADS_PER_REPLICA: usize = 256;


verus!{


struct_with_invariants!{
    /// An entry that sits on the log. Each entry consists of three fields: The operation to
    /// be performed when a thread reaches this entry on the log, the replica that appended
    /// this operation, and a flag indicating whether this entry is valid.
    ///
    /// `T` is the type on the operation - typically an enum class containing opcodes as well
    /// as arguments. It is required that this type be sized and cloneable.
    #[repr(align(128))]
    pub struct BufferEntry {
        /// The operation that this entry represents.
        ///
        ///  - Dafny: linear cell: Cell<CB.ConcreteLogEntry>, where
        ///            datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
        ///  - Rust:  pub(crate) operation: Option<T>,
        // pub(crate) operation: Option<UOp>,

        /// Identifies the replica that issued the above operation.
        ///
        ///  - Dafny: as part of ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
        ///  - Rust:  pub(crate) replica: usize,
        // pub(crate) replica: usize,
        //

        pub log_entry: PCell<LogEntry>,

        // / Indicates whether this entry represents a valid operation when on the log.
        // /
        // /  - Dafny: linear alive: Atomic<bool, CBAliveBit>)
        // /  - Rust:  pub(crate) alivef: AtomicBool,
        alive: AtomicBool<_, CyclicBuffer::alive_bits, _>,

        #[verifier::spec] cyclic_buffer_idx: nat,

        #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
    }

    pub closed spec fn wf(&self, i: nat) -> bool {
        invariant on alive with (cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits) {
            // g@ === CyclicBuffer::token![ cyclic_buffer_instance => alive_bits ]
            true
        }
    }

    // pub closed spec fn wf(&self) -> bool {
    //     invariant on alive with (cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits) {
    //         g@ === CyclicBuffer::token![ cyclic_buffer_instance => version_upper_bound => v as nat ]
    //     }
    // }
}


struct_with_invariants!{
/// A log of operations that is typically accessed by multiple Replicas/Nodes
///
/// Corresponds to
///  - `pub struct Log<T, LM, M>` in the upstream code
///  - `linear datatype NR` in the dafny code
#[repr(align(128))]
pub struct NrLog
{
    // /// The actual log, a slice of entries.
    // ///  - Dafny: linear buffer: lseq<BufferEntry>,
    // ///           glinear bufferContents: GhostAtomic<CBContents>,
    // ///  - Rust:  pub(crate) slog: Box<[Cell<Entry<T, M>>]>,
    slog: Vec<BufferEntry>,

    /// Completed tail maintains an index <= tail that points to a log entry after which there
    /// are no completed operations across all replicas registered against this log.
    ///
    ///  - Dafny: linear ctail: CachePadded<Atomic<uint64, Ctail>>,
    ///  - Rust:  pub(crate) ctail: CachePadded<AtomicUsize>,
    version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound, _>>,

    /// Logical index into the above slice at which the log starts.
    ///
    ///  - Dafny: linear head: CachePadded<Atomic<uint64, CBHead>>,
    ///  - Rust:  pub(crate) head: CachePadded<AtomicUsize>,
    head: CachePadded<AtomicU64<_, CyclicBuffer::head, _>>,

    /// Logical index into the above slice at which the log ends. New appends go here.
    ///
    ///  - Dafny: linear globalTail: CachePadded<Atomic<uint64, GlobalTailTokens>>,
    ///  - Rust:  pub(crate) tail: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicU64<_, (UnboundedLog::tail, CyclicBuffer::tail), _>>,

    /// Array consisting of the local tail of each replica registered with the log.
    /// Required for garbage collection; since replicas make progress over the log
    /// independently, we want to make sure that we don't garbage collect operations
    /// that haven't been executed by all replicas.
    ///
    ///  - Dafny: linear node_info: lseq<NodeInfo>, // NodeInfo is padded
    ///  - Rust:  pub(crate) ltails: [CachePadded<AtomicUsize>; MAX_REPLICAS_PER_LOG],
    ///
    /// XXX: should we make this an array as well
    pub(crate) local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions, CyclicBuffer::local_versions), _>>>,  // NodeInfo is padded


    // The upstream Rust version also contains:
    //  - pub(crate) next: CachePadded<AtomicUsize>, the identifier for the next replica
    //  - pub(crate) lmasks: [CachePadded<Cell<bool>>; MAX_REPLICAS_PER_LOG], tracking of alivebits


    // #[verifier::proof] local_reads: Map<ReqId, ReadonlyState>,  // ghost
    // #[verifier::proof] local_reads: UnboundedLog::local_reads,

    // ghost cb_loc_s: nat
    // ...

    #[verifier::proof] unbounded_log_instance: UnboundedLog::Instance,
    #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
}

pub closed spec fn wf(&self) -> bool {
    predicate {
        // TODO from example, replace
        // TODO &&& self.instance.backing_cells().len() == self.buffer@.len()
        // TODO &&& (forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
        // TODO     self.instance.backing_cells().index(i) ===
        // TODO         self.buffer@.index(i).id())

        // |node_info| == NUM_REPLICAS as int
        &&& self.local_versions.len() == NUM_REPLICAS

        // |buffer| == LOG_SIZE as int
        &&& self.slog.len() == LOG_SIZE

        // (forall i: nat | 0 <= i < LOG_SIZE as int :: buffer[i].WF(i, cb_loc_s))
        &&& (forall |i: nat| i < LOG_SIZE ==> #[trigger] self.slog[i as int].wf(i))
    }

    // invariant on slog with (

    invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound) {
        // (forall v, g :: atomic_inv(ctail.inner, v, g) <==> g == Ctail(v as int))
        g@ === UnboundedLog::token![ unbounded_log_instance => version_upper_bound => v as nat ]
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head) {
        // (forall v, g :: atomic_inv(head.inner, v, g) <==> g == CBHead(v as int, cb_loc_s))
        g@ === CyclicBuffer::token![ cyclic_buffer_instance => head => v as nat ]
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail, CyclicBuffer::tail)) {
        // (forall v, g :: atomic_inv(globalTail.inner, v, g) <==> GlobalTailInv(v, g, cb_loc_s))
        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance => tail => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance => tail => v as nat ]
    }


    // (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId, cb_loc_s))
    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_versions)) {


        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance => local_versions => i as nat => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance => local_versions => i as nat => v as nat ]
        &&& 0 <= v < 0xffff_ffff_f000_0000
    }

    // invariant on local_reads with (unbounded_log_instance)
    //     forall |i: int|
    //     where (0 <= i < self.local_reads@.contains())
    //     is (v: Map<ReqId, ReadonlyState>, g: UnboundedLog::local_reads) {
    //     g@ === UnboundedLog::token![ unbounded_log_instance => local_reads => v ]
    // }

}
} // struct_with_invariants!{


// CachePadded<
//     pervasive::atomic_ghost::AtomicU64<
//         (spec::unbounded_log::UnboundedLog::Instance, spec::cyclicbuffer::CyclicBuffer::Instance, builtin::int),
//         (spec::unbounded_log::UnboundedLog::local_versions, spec::cyclicbuffer::CyclicBuffer::local_versions),
//         InvariantPredicate_auto_NrLog_local_versions
//     >
// >

impl NrLog
{
    // pub fn new() -> Self {
    //     Self {
    //         // head: CachePadded::new(AtomicUsize::new(0)),
    //         head: CachePadded::new(AtomicU64::new(0)),
    //         // tail: CachePadded::new(AtomicUsize::new(0)),
    //         tail: CachePadded::new(AtomicU64::new(0)),

    //         version_upper_bound: CachePadded::new(AtomicU64::new(0)),
    //         local_versions: Vec::new(),
    //         // local_reads: Map::new(),
    //         local_reads: Map::new(),
    //         // cb_loc_s: 0,
    //         // unbounded_log_instance: UnboundedLog::Instance::new(),
    //         // cyclic_buffer_instance: CyclicBuffer::Instance::new(),
    //         // unbounded_log_instance: UnboundedLog::Instance::new(),
    //         // cyclic_buffer_instance: CyclicBuffer::Instance::new(),
    //     }
    // }


    /// checks whether the version of the local replica has advanced enough to perform read operations
    ///
    /// This basically corresponds to the transition `readonly_read_to_read` in the unbounded log.
    ///
    // https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/log.rs#L525
    pub fn is_replica_synced_for_reads(&self, node_id: usize, version_upper_bound: u64,
            tracked local_reads: UnboundedLog::local_reads) ->
            // (bool,  UnboundedLog::local_reads)
            // (bool, Tracked<UnboundedLog::local_reads>)
            bool


        requires
          self.wf(),
          node_id < self.local_versions.len()
        //   old(self).unbounded_log_instance.local_reads[]
        // TODO: more stuff here
    {
        // obtain the local version
        let local_version = &self.local_versions.index(node_id).0;

        // #[verifier::proof]
        let rid : u64 = 0; // XXX: where to get that from?


        proof {
            let tracked new_local_reads: UnboundedLog::local_reads;
        }

        let res = 0;
        // TODO ask @tjhance let res = atomic_with_ghost!(
        // TODO ask @tjhance     local_version => load();
        // TODO ask @tjhance     returning res;
        // TODO ask @tjhance     ghost g => {
        // TODO ask @tjhance         new_local_reads = if res >= version_upper_bound {
        // TODO ask @tjhance             self.unbounded_log_instance.readonly_ready_to_read(rid as nat, node_id as NodeId, &g.0, local_reads)
        // TODO ask @tjhance         } else {
        // TODO ask @tjhance             local_reads
        // TODO ask @tjhance         };
        // TODO ask @tjhance     }
        // TODO ask @tjhance );

        // (res >= version_upper_bound, local_reads);
        res >= version_upper_bound
    }




}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Contexts
////////////////////////////////////////////////////////////////////////////////////////////////////

// TODO:
pub struct RwLock<D>
{
    foo: Option<D>
}


/// the thread token identifies a thread of a given replica
pub struct ThreadToken {
    /// the replica id this thread uses
    pub(crate) rid: ReplicaId,
    /// identifies the thread within the replica
    pub(crate) tid: ReplicaToken,
}

pub struct LogToken {
    id: usize
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Contexts
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Data for a pending operation.
///
///  - Dafny: datatype OpResponse
///  - Rust:  pub struct PendingOperation<T, R, M> {
///
/// In Dafny those data types are not options, but in Rust they are
pub struct PendingOperation<UOp, Res> {
    /// the operation that is being executed
    pub(crate) op: Option<UOp>,
    /// the response of the operation
    pub(crate) resp: Option<Res>,
}

struct_with_invariants!{
pub struct ContextGhost<UOp, Res> {
    /// Token to access the batch cell in Context
    ///
    ///  - Dafny: glinear contents: glOption<CellContents<OpResponse>>,
    batch_token: Tracked<PermissionOpt<PendingOperation<UOp, Res>>>,

    //
    // fc: FCSlot

    // update: UpdateTicket?

}
pub closed spec fn inv(&self, v: u64, i: nat, cell: PCell<PendingOperation<UOp, Res>>) -> bool {

}
} // struct_with_invariants! ContextGhost


struct_with_invariants!{
/// Contains state of a particular thread w.r.g. to outstanding operations.
///
///  - Dafny: linear datatype Context
///  - Rust:  pub(crate) struct Context<T, R, M>
///
/// Note, in contrast to the Rust version, we just have a single outstanding operation
#[repr(align(128))]
pub struct Context<UOp, Res> {
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    ///
    ///  - Dafny: linear cell: CachePadded<Cell<OpResponse>>
    ///  - Rust:  pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],
    batch: CachePadded<PCell<PendingOperation<UOp, Res>>>,

    /// maybe some kind of lock?
    ///  - Dafny: linear atomic: CachePadded<Atomic<uint64, ContextGhost>>,
    ///  - Rust:  N/A
    atomic: CachePadded<AtomicU64<_, ContextGhost<UOp, Res>, _>>,
}

pub closed spec fn wf(&self, i: nat) -> bool {
    predicate {
        true
    }

    invariant on atomic specifically (self.atomic.0) is (v: u64, g: ContextGhost<UOp, Res>) {
      // (forall v, g :: atomic_inv(atomic.inner, v, g) <==> g.inv(v, i, cell.inner, fc_loc))
      // atomic.atomic_inv() <==> g.inv(v, i, self.batch)
      true
    }
}

} // struct_with_invariants!


////////////////////////////////////////////////////////////////////////////////////////////////////
// The Replica Node
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A token handed out to threads that replicas with replicas.
// #[derive(Copy, Clone, Eq, PartialEq)]
// pub struct ReplicaToken {
//     pub(crate) tid: ThreadIdx,
// }

pub type ReplicaToken = ThreadIdx;


/// Ghost state that is protected by the combiner lock
///
///  - Dafny: glinear datatype CombinerLockState
///  - Rust:  N/A
pub struct CombinerLockStateGhost {
    // TODO
    // glinear flatCombiner: FCCombiner,

    /// Stores the token to access the op_buffer in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    op_buffer_token: Tracked<PermissionOpt<Vec<UpdateOp>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    responses_token: Tracked<PermissionOpt<Vec<ReturnType>>>,
}

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
    log_tkn: LogToken,

    /// Stores the index of the thread currently doing flat combining. Field is
    /// zero if there isn't any thread actively performing flat-combining.
    /// Atomic since this acts as the combiner lock.
    ///
    ///  - Dafny: linear combiner_lock: CachePadded<Atomic<uint64, glOption<CombinerLockState>>>,
    ///  - Rust:  combiner: CachePadded<AtomicUsize>,
    combiner: CachePadded<AtomicU64<_, Option<CombinerLockStateGhost>, _>>,

    /// List of per-thread contexts. Threads buffer write operations here when
    /// they cannot perform flat combining (because another thread might already
    /// be doing so).
    ///
    ///  - Dafny: linear contexts: lseq<Context>,
    ///  - Rust:  contexts: Vec<Context<<D as Dispatch>::WriteOperation, <D as Dispatch>::Response>>,
    contexts: Vec<Context<UpdateOp, ReturnType>>,

    /// A buffer of operations for flat combining.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
    ///  - Rust:  buffer: RefCell<Vec<<D as Dispatch>::WriteOperation>>,
    op_buffer: PCell<Vec<UpdateOp>>,

    /// A buffer of results collected after flat combining. With the help of
    /// `inflight`, the combiner enqueues these results into the appropriate
    /// thread context.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear responses: LC.LinearCell<seq<nrifc.ReturnType>>,
    ///  - Rust:  result: RefCell<Vec<<D as Dispatch>::Response>>,
    responses: PCell<Vec<ReturnType>>,


    // The underlying data structure. This is shared among all threads that are
    // registered with this replica. Each replica maintains its own copy of
    // `data`.
    //
    //   - Dafny: linear replica: RwLock,
    //   - Rust:  data: CachePadded<RwLock<D>>,
    data: CachePadded<RwLock<NRState>>,


    // /// Thread index that will be handed out to the next thread that registers
    // /// with the replica when calling [`Replica::register()`].
    // next: CachePadded<AtomicUsize>,
    // /// Number of operations collected by the combiner from each thread at any
    // inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,

    #[verifier::proof] unbounded_log_instance: UnboundedLog::Instance,
    #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
}

pub closed spec fn wf(&self, log: &NrLog) -> bool {

    // && (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int, nr.cb_loc_s))


    // invariant on the RwLock inner data structure
    // && replica.InternalInv()

    predicate {
        // && (forall i | 0 <= i < |contexts| :: i in contexts && contexts[i].WF(i, fc_loc))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> #[trigger] self.contexts[i as int].wf(i))
        // && |contexts| == MAX_THREADS_PER_REPLICA as int
        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        // && 0 <= nodeId as int < NUM_REPLICAS as int
        &&& 0 <= self.log_tkn.id < NUM_REPLICAS
    }

    invariant on combiner specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost>) {

        // && (forall v, g :: atomic_inv(combiner_lock.inner, v, g) <==> CombinerLockInv(v, g, fc_loc, ops, responses))
        if v == 0 {
            // the lock is not taken,
            &&& g.is_Some()
        } else {
            // the lock is taken
            &&& g.is_None()
        }
    }
}

} // struct_with_invariants!


impl Replica  {

    /// Try to become acquire the combiner lock here. If this fails, then return None.
    ///
    ///  - Dafny: part of method try_combine
    #[inline(always)]
    fn acquire_combiner_lock(&self) -> Option<CombinerLockStateGhost> {
        // OPT: try to check whether the lock is already present
        // for _ in 0..4 {
        //     if self.combiner.load(Ordering::Relaxed) != 0 { return None; }
        // }

        // Step 1: perform cmpxchg to acquire the combiner lock
        // if self.combiner.compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Acquire) != Ok(0) {
        //     None
        // } else {
        //     Some(CombinerLock { replica: self })
        // }
        assert(false);
        None
    }

    /// Appends an operation to the log and attempts to perform flat combining.
    /// Accepts a thread `tid` as an argument. Required to acquire the combiner lock.
    ///
    /// https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/nr/replica.rs#L788
    fn try_combine(&self, slog: &NrLog) {
        // Step 1: try to take the combiner lock to become combiner
        // let combiner_lock = self.acquire_combiner_lock();

        // Step 2: if we are the combiner then perform flat combining, else return
        // if let Some(combiner_lock) = combiner_lock {
        //     self.combine(slog, combiner_lock)
        // } else {
        //     // just return, that means another thread is combining already
        //     Ok(())
        // }

        // release the combiner lock
    }

    /// Performs one round of flat combining. Collects, appends and executes operations.
    ///
    /// https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/nr/replica.rs#L835
    fn combine(&self, slog: &NrLog, tracked combiner_lock: CombinerLockStateGhost)  {
        // Step 1: collect the operations from the threads
        // self.collect_thread_ops(&mut buffer, operations.as_mut_slice());

        // Step 2: Append all operations to the log

        // Step 3: Take the R/W lock on the data structure

        // Step 3: Execute all operations

        // Step 4: release the R/W lock on the data structure

        // Step 5: collect the results


    }

    ///
    /// - Dafny: combine_collect()
    #[inline(always)]
    fn collect_thread_ops(&self, buffer: &mut Vec<UpdateOp>, operations: &mut [usize]) {
        // let num_registered_threads = self.next.load(Ordering::Relaxed);

        // // Collect operations from each thread registered with this replica.
        // for i in 1..num_registered_threads {
        //     let ctxt_iter = self.contexts[i - 1].iter();
        //     operations[i - 1] = ctxt_iter.len();
        //     // meta-data is (), throw it away
        //     buffer.extend(ctxt_iter.map(|op| op.0));
        // }
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
          self.wf(slog),
          slog.wf(),
    {
        proof {
            // start the read transaction, get the ticket
            let tracked ticket = self.unbounded_log_instance.readonly_start(op);
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
            self.wf(slog)
            // something about the idx
    {
        proof {
            let tracked ticket = self.unbounded_log_instance.update_start(op);
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


////////////////////////////////////////////////////////////////////////////////////////////////////
// The Public Interface
////////////////////////////////////////////////////////////////////////////////////////////////////


/// The "main" type of NR which users interact with.
///
///  - Dafny: N/A
///  - Rust:  pub struct NodeReplicated<D: Dispatch + Sync>
pub struct NodeReplicated {
    /// the log of operations
    ///
    ///  - Rust: log: Log<D::WriteOperation>,
    log: NrLog,
    // log: NrLog,

    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<NRState, UpdateOp, ReturnType>>>,
    replicas: Vec<Box<Replica>>,

    /// something that creates new request ids, or do we
    // #[verifier::proof] request_id: ReqId,

    #[verifier::proof] unbounded_log_instance: UnboundedLog::Instance,
    #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
}



/// Proof blocks for the NodeReplicate data structure
impl NodeReplicated {
    pub closed spec fn wf(&self) -> bool {
        &&& self.log.wf()
        &&& self.unbounded_log_instance == self.log.unbounded_log_instance
        &&& self.cyclic_buffer_instance == self.log.cyclic_buffer_instance

        &&& forall |i| 0 <= i < self.replicas.len() ==> {
            &&& #[trigger] self.replicas[i].wf(&self.log)
            &&& self.replicas[i].unbounded_log_instance == self.unbounded_log_instance
            &&& self.replicas[i].cyclic_buffer_instance == self.cyclic_buffer_instance
        }
    }
}


impl NodeReplicated {
    // /// Creates a new, replicated data-structure from a single-threaded
    // /// data-structure that implements [`Dispatch`]. It uses the [`Default`]
    // /// constructor to create a initial data-structure for `D` on all replicas.
    // ///
    // ///  - Dafny: n/a ?
    // ///  - Rust:  pub fn new(num_replicas: NonZeroUsize) -> Result<Self, NodeReplicatedError>
    // pub fn init(num_replicas: usize) -> Self
    //     requires num_replicas > 0
    // {

    //     // This is basically a wrapper around the `init` of the interface defined in Dafny

    //     // allocate a new log

    //     // register the replicas with the log

    //     // add the replica to the list of replicas
    //     // unimplemented!()
    //     assert(false);

    //     NodeReplicated {
    //         log: NrLog::new(),
    //         replicas: Vec::new(),
    //     }
    // }

    /// Registers a thread with a given replica in the [`NodeReplicated`]
    /// data-structure. Returns an Option containing a [`ThreadToken`] if the
    /// registration was successful. None if the registration failed.
    ///
    /// XXX: in the dafny version, we don't have this. Instead, we pre-allocate all
    ///      threads for the replicas etc.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken>
    pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken>
        requires self.wf()
    {
        assert(false);
        None
    }

    /// Executes a mutable operation against the data-structure.
    ///
    ///  - Dafny:
    ///  - Rust:  pub fn execute_mut(&self, op: <D as Dispatch>::WriteOperation, tkn: ThreadToken)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    pub fn execute_mut(&self, op: UpdateOp, tkn: ThreadToken) -> Result<ReturnType, ()>
        requires
          self.wf()
    {
        if tkn.rid < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            self.replicas.index(tkn.rid).execute_mut(&self.log, op, tkn.tid)
        } else {
            Err(())
        }
    }


    /// Executes a immutable operation against the data-structure.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn execute(&self, op: <D as Dispatch>::ReadOperation<'_>, tkn: ThreadToken,)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    pub fn execute(&self, op: ReadonlyOp, tkn: ThreadToken) -> Result<ReturnType, ()>
        requires self.wf()
    {
        if tkn.rid < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            self.replicas.index(tkn.rid).execute(&self.log, op, tkn.tid)
        } else {
            Err(())
        }
    }
}


} // verus!


pub fn main() {}
