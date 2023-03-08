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
    pub struct LogEntry<UOp> {
        /// The operation that this entry represents.
        ///
        ///  - Dafny: linear cell: Cell<CB.ConcreteLogEntry>, where
        ///            datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
        ///  - Rust:  pub(crate) operation: Option<T>,
        pub(crate) operation: Option<UOp>,

        /// Identifies the replica that issued the above operation.
        ///
        ///  - Dafny: as part of ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
        ///  - Rust:  pub(crate) replica: usize,
        pub(crate) replica: usize,

        // / Indicates whether this entry represents a valid operation when on the log.
        // /
        // /  - Dafny: linear alive: Atomic<bool, CBAliveBit>)
        // /  - Rust:  pub(crate) alivef: AtomicBool,
        // alive: AtomicU64<_, CyclicBuffer::alive_bits, _>,

        // #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
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
// pub struct NrLog
struct NrLog<UOp>
{
    // /// The actual log, a slice of entries.
    // ///  - Dafny: linear buffer: lseq<BufferEntry>,
    // ///           glinear bufferContents: GhostAtomic<CBContents>,
    // ///  - Rust:  pub(crate) slog: Box<[Cell<Entry<T, M>>]>,
    slog: Box<PCell<LogEntry<UOp>>>,

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
    local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions, CyclicBuffer::local_versions), _>>>,  // NodeInfo is padded


    // The upstream Rust version also contains:
    //  - pub(crate) next: CachePadded<AtomicUsize>, the identifier for the next replica
    //  - pub(crate) lmasks: [CachePadded<Cell<bool>>; MAX_REPLICAS_PER_LOG], tracking of alivebits


    // #[verifier::proof] local_reads: Map<ReqId, ReadonlyState>,  // ghost

    #[verifier::proof] local_reads: UnboundedLog::local_reads,

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
        true

        // |node_info| == NUM_REPLICAS as int
        &&& self.local_versions.len() == NUM_REPLICAS

        // |buffer| == LOG_SIZE as int
        // &&& self.slog.len() == LOG_SIZE

        // (forall i: nat | 0 <= i < LOG_SIZE as int :: buffer[i].WF(i, cb_loc_s))
        &&& (forall |i| 0 <= i < LOG_SIZE ==> self.slog[i].wf(i))
    }

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

impl<UOp> NrLog<UOp>
// impl NrLog
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
    pub fn is_replica_synced_for_reads(&mut self, node_id: usize, version_upper_bound: u64) -> bool

        requires
          old(self).wf(),
        //   old(self).unbounded_log_instance.local_reads[]
        // TODO: more stuff here
    {
        // obtain the local version
        let local_version = &self.local_versions.index(node_id).0;

        // #[verifier::proof]
        let rid : u64 = 0; // XXX: where to get that from?



        #[verifier::proof]
        let new_local_reads: Option<UnboundedLog::local_reads>;

        //  self.ltails[idx.0 - 1].load(Ordering::Relaxed) >= ctail
        let res = atomic_with_ghost!(
            local_version => load();
            returning res;
            ghost g => {
                new_local_reads = if res >= version_upper_bound {
                    // XXX: is that the right thing to do with local_reads, or do they need to be obtained differently?
                    #[verifier::proof] let new_local_reads = self.unbounded_log_instance.readonly_ready_to_read(rid as nat, node_id as NodeId, &g.0, self.local_reads);
                    Option::Some(new_local_reads)
                } else {
                    Option::None
                };

                // assert(ret as nat == g.1.index(node_id));
            }
        );

        if let Some(lrds) = new_local_reads {
            // the change has happened

            self.local_reads = lrds;

        } else {
            // no change at all
        }

        res >= version_upper_bound
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Contexts
////////////////////////////////////////////////////////////////////////////////////////////////////

// TODO:
struct RwLock<D>
{
    foo: Option<D>
}


pub struct ThreadToken {}
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
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct ReplicaToken {
    pub(crate) tid: ThreadIdx,
}


/// Ghost state that is protected by the combiner lock
///
///  - Dafny: glinear datatype CombinerLockState
///  - Rust:  N/A
pub struct CombinerLockStateGhost<UOp, Res> {
    // TODO
    // glinear flatCombiner: FCCombiner,

    /// Stores the token to access the op_buffer in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    op_buffer_token: Tracked<PermissionOpt<Vec<UOp>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    responses_token: Tracked<PermissionOpt<Vec<Res>>>,
}

struct_with_invariants!{
/// An instance of a replicated data structure which uses a shared [`Log`] to
/// scale operations on the data structure across cores and processors.
///
///  - Dafny:   linear datatype Node
///  - Rust:    pub struct Replica<D>
#[repr(align(128))]
// pub struct Replica<D, UOp, Res> {   // XXX: why unconstrained type parameter?
pub struct Replica< UOp, Res> {
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
    combiner: CachePadded<AtomicU64<_, Option<CombinerLockStateGhost<UOp, Res>>, _>>,

    /// List of per-thread contexts. Threads buffer write operations here when
    /// they cannot perform flat combining (because another thread might already
    /// be doing so).
    ///
    ///  - Dafny: linear contexts: lseq<Context>,
    ///  - Rust:  contexts: Vec<Context<<D as Dispatch>::WriteOperation, <D as Dispatch>::Response>>,
    contexts: Vec<Context<UOp, Res>>,

    /// A buffer of operations for flat combining.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
    ///  - Rust:  buffer: RefCell<Vec<<D as Dispatch>::WriteOperation>>,
    op_buffer: PCell<Vec<UOp>>,

    /// A buffer of results collected after flat combining. With the help of
    /// `inflight`, the combiner enqueues these results into the appropriate
    /// thread context.
    ///
    /// Safety: Protected by the cominer lock.
    ///
    ///  - Dafny: linear responses: LC.LinearCell<seq<nrifc.ReturnType>>,
    ///  - Rust:  result: RefCell<Vec<<D as Dispatch>::Response>>,
    responses: PCell<Vec<Res>>,


    // The underlying data structure. This is shared among all threads that are
    // registered with this replica. Each replica maintains its own copy of
    // `data`.
    //
    //   - Dafny: linear replica: RwLock,
    //   - Rust:  data: CachePadded<RwLock<D>>,
    // data: CachePadded<RwLock<D>>,


    // /// Thread index that will be handed out to the next thread that registers
    // /// with the replica when calling [`Replica::register()`].
    // next: CachePadded<AtomicUsize>,
    // /// Number of operations collected by the combiner from each thread at any
    // inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,
}

pub closed spec fn wf(&self, log: NrLog<UOp>) -> bool {

    // && (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int, nr.cb_loc_s))


    // invariant on the RwLock inner data structure
    // && replica.InternalInv()

    predicate {
        // && (forall i | 0 <= i < |contexts| :: i in contexts && contexts[i].WF(i, fc_loc))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> self.contexts[i as int].wf(i))
        // && |contexts| == MAX_THREADS_PER_REPLICA as int
        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        // && 0 <= nodeId as int < NUM_REPLICAS as int
        &&& 0 <= self.log_tkn.id < NUM_REPLICAS
    }

    invariant on combiner specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost <UOp, Res>>) {

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
    log: NrLog<UpdateOp>,
    // log: NrLog,

    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<NRState, UpdateOp, ReturnType>>>,
    replicas: Vec<Box<Replica<UpdateOp, ReturnType>>>,
}


//impl<D> NodeReplicated<D> {
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
    ///  - Dafny: n/a?
    ///  - Rust:  pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken>
    pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken> {
        assert(false);
        None
    }

    /// Executes a mutable operation against the data-structure.
    ///
    ///  - Dafny:
    ///  - Rust:  pub fn execute_mut(&self, op: <D as Dispatch>::WriteOperation, tkn: ThreadToken)
    ///             -> <D as Dispatch>::Response
    pub fn execute_mut(&self, op: UpdateOp, tkn: ThreadToken) -> ReturnType {
        // This is basically a wrapper around the `do_operation` of the interface defined in Dafny
        assert(false);
        ReturnType { u: 0 }
    }


    /// Executes a immutable operation against the data-structure.
    ///
    ///  - Dafny:
    ///  - Rust:  pub fn execute(&self, op: <D as Dispatch>::ReadOperation<'_>, tkn: ThreadToken,)
    ///             -> <D as Dispatch>::Response {
    pub fn execute(&self, op: ReadonlyOp, tkn: ThreadToken) -> ReturnType {
        // This is basically a wrapper around the `do_operation` of the interface defined in Dafny
        assert(false);
        ReturnType { u: 0 }
    }
}


} // verus!


pub fn main() {}
