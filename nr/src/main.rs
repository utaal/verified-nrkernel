// the verus dependencies
#[macro_use]
mod pervasive;
use pervasive::prelude::*;

use pervasive::cell::{PCell, PermissionOpt};
use pervasive::map::Map;
use pervasive::option::Option;
use pervasive::vec::Vec;

mod spec;
// mod exec;

use spec::cyclicbuffer::CyclicBuffer;
use spec::flat_combiner::FlatCombiner;
use spec::types::*;
use spec::unbounded_log::UnboundedLog;

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

verus_old_todo_no_ghost_blocks! {


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
    pub slog: Vec<BufferEntry>,

    /// Completed tail maintains an index <= tail that points to a log entry after which there
    /// are no completed operations across all replicas registered against this log.
    ///
    ///  - Dafny: linear ctail: CachePadded<Atomic<uint64, Ctail>>,
    ///  - Rust:  pub(crate) ctail: CachePadded<AtomicUsize>,
    pub version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound, _>>,

    /// Logical index into the above slice at which the log starts.
    ///
    ///  - Dafny: linear head: CachePadded<Atomic<uint64, CBHead>>,
    ///  - Rust:  pub(crate) head: CachePadded<AtomicUsize>,
    pub head: CachePadded<AtomicU64<_, CyclicBuffer::head, _>>,

    /// Logical index into the above slice at which the log ends. New appends go here.
    ///
    ///  - Dafny: linear globalTail: CachePadded<Atomic<uint64, GlobalTailTokens>>,
    ///  - Rust:  pub(crate) tail: CachePadded<AtomicUsize>,
    pub tail: CachePadded<AtomicU64<_, (UnboundedLog::tail, CyclicBuffer::tail), _>>,

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

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
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
        g@ === UnboundedLog::token![ unbounded_log_instance@ => version_upper_bound => v as nat ]
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head) {
        // (forall v, g :: atomic_inv(head.inner, v, g) <==> g == CBHead(v as int, cb_loc_s))
        g@ === CyclicBuffer::token![ cyclic_buffer_instance@ => head => v as nat ]
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail, CyclicBuffer::tail)) {
        // (forall v, g :: atomic_inv(globalTail.inner, v, g) <==> GlobalTailInv(v, g, cb_loc_s))
        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance@ => tail => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance@ => tail => v as nat ]
    }


    // (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId, cb_loc_s))
    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_versions)) {


        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance@ => local_versions => i as nat => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance@ => local_versions => i as nat => v as nat ]
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
                                       tracked local_reads: Tracked<UnboundedLog::local_reads>)
            -> (result: (bool, Tracked<UnboundedLog::local_reads>))
        requires
            self.wf(),
            node_id < self.local_versions.len(),
            local_reads@@.instance == self.unbounded_log_instance@,
            local_reads@@.value.is_VersionUpperBound(),
            local_reads@@.value.get_VersionUpperBound_version_upper_bound() == version_upper_bound
        ensures
            result.0 ==> result.1@@.value.is_ReadyToRead(),
            !result.0 ==> result.1 == local_reads
    {
        // obtain the request id from the local_reads token
        let rid_g : Ghost<ReqId> = ghost(local_reads@@.key);
        let tracked new_local_reads_g: UnboundedLog::local_reads;

        // obtain the local version
        let local_version = &self.local_versions.index(node_id).0;

        let res = atomic_with_ghost!(
            local_version => load();
            returning res;
            ghost g => {
                new_local_reads_g = if res >= version_upper_bound {
                    self.unbounded_log_instance
                        .borrow()
                        .readonly_ready_to_read(rid_g.view(), node_id as NodeId, &g.0, local_reads.get())
                } else {
                    local_reads.get()
                };
            }
        );

        (res >= version_upper_bound, tracked(new_local_reads_g))
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
pub struct PendingOperation {
    /// the operation that is being executed
    pub(crate) op: Option<UpdateOp>,
    /// the response of the operation
    pub(crate) resp: Option<ReturnType>,
}

impl PendingOperation {
    // pub fn new(op: UpdateOp) -> Self {
    //     Self {
    //         op: Some(op),
    //         resp: None,
    //     }
    // }

    pub fn set_result(&mut self, resp: ReturnType) {
        self.resp = Some(resp);
    }

    // pub fn to_result(self) -> ReturnType {
    //     self.resp.get_Some_0()
    // }
}

struct_with_invariants!{
pub struct ContextGhost {
    /// Token to access the batch cell in Context
    ///
    ///  - Dafny: glinear contents: glOption<CellContents<OpResponse>>,
    pub batch_token: Tracked<PermissionOpt<PendingOperation>>,

    // The flat combiner
    // fc: FCSlot
    pub flat_combiner_slots: FlatCombiner::slots,

    // update: UpdateTicket?
    pub update: Tracked<UnboundedLog::local_updates>
}

pub closed spec fn inv(&self, v: u64, i: nat, cell: PCell<PendingOperation>) -> bool {

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
pub struct Context {
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    ///
    ///  - Dafny: linear cell: CachePadded<Cell<OpResponse>>
    ///  - Rust:  pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],
    batch: CachePadded<PCell<PendingOperation>>,

    /// maybe some kind of lock?
    ///  - Dafny: linear atomic: CachePadded<Atomic<uint64, ContextGhost>>,
    ///  - Rust:  N/A
    atomic: CachePadded<AtomicU64<_, ContextGhost, _>>,

    /// ghost
    pub thread_id_g: Tracked<ThreadToken>,
}

pub closed spec fn wf(&self) -> bool {
    predicate {
        true
    }

    invariant on atomic specifically (self.atomic.0) is (v: u64, g: ContextGhost) {
      // (forall v, g :: atomic_inv(atomic.inner, v, g) <==> g.inv(v, i, cell.inner, fc_loc))
      // atomic.atomic_inv() <==> g.inv(v, i, self.batch)
      &&& (v == 0) <==> g.batch_token@@.value.is_None()
    }
}} // struct_with_invariants!

impl Context {

    pub open spec fn get_thread_id(&self) -> nat {
        self.thread_id_g@.tid as nat
    }

    /// Enqueues an operation onto this context's batch of pending operations.
    pub fn enqueue_op(&self, op: UpdateOp, tracked update: Tracked<UnboundedLog::local_updates>)
        -> bool
        requires self.wf()
    {
        // enqueue is a bit a misnomer here, we actually only have one slot in the batch for now.

        // let tracked token : Option<Tracked<PermissionOpt<PendingOperation>>>;
        // let res = atomic_with_ghost!(
        //     &self.atomic.0 => compare_exchange(0, 1);
        //     update prev->next;
        //     ghost g => {
        //         if prev == 0 {
        //             // store the operatin in the cell
        //             token =  Some(g.batch_token);
        //         } else {
        //             token = None;
        //         }
        //     }
        // );

        // if res.is_Ok() {
        //     if res.get_Ok_0() == 0 {
        //         let tracked token = token.get_Some_0();
        //         let pending_op = PendingOperation {
        //             op: Some(op),
        //             resp: None,
        //         };

        //         // HERE:
        //         // self.batch.0.put(&mut token, pending_op);
        //         true
        //     } else {
        //         false
        //     }
        // } else {
        //     false
        // }
        false
    }

    /// Enqueues a response onto this context. This is invoked by the combiner
    /// after it has executed operations (obtained through a call to ops()) against the
    /// replica this thread is registered against.
    pub fn enqueue_response(&self, resp: ReturnType) -> bool
        requires
            self.wf(),
            // self.atomic != 0
    {
        // let tracked token : Option<Tracked<PermissionOpt<PendingOperation>>>;
        // let res = atomic_with_ghost!(
        //     &self.atomic.0 => load();
        //     returning res;
        //     ghost g => {
        //         if res == 1 {
        //             // store the operatin in the cell
        //             token =  Some(g.batch_token);
        //         } else {
        //             token = None;
        //         }
        //     }
        // );

        // if res != 0 {
        //     let tracked token = token.get_Some_0();
        //     // take the operation from the cell
        //     // HERE
        //     // let mut prev = self.batch.0.take(&mut token);
        //     // prev.set_result(resp);
        //     // store the operation in the cell again
        //     // self.batch.0.put(&mut token, prev);

        //     true
        // } else {
        //     false
        // }

        false
    }

    /// Returns a single response if available. Otherwise, returns None.
    pub fn get_result(&self) -> Option<ReturnType>
        requires self.wf()
    {
        // let tracked token : Option<Tracked<PermissionOpt<PendingOperation>>>;
        // // let res = atomic_with_ghost!(
        // //     &self.atomic.0 => compare_exchange(1, 0);
        // //     update prev->next;
        // //     ghost g => {
        // //         if prev == 1 {
        // //             // store the operatin in the cell
        // //             token =  Some(g.batch_token);
        // //         } else {
        // //             token = None;
        // //         }
        // //     }
        // // );

        // if res.get_Ok_0() != 0 {
        //     // let pending_op = self.batch.0.take(token.get_Some_0());
        //     // let response = pending_op.resp.get_Some_0();
        //     // Some(response)
        //     None
        // } else {
        //     None
        // }
        None
    }

    /// Returns the maximum number of operations that will go pending on this context.
    #[inline(always)]
    pub(crate) fn batch_size() -> usize {
        // MAX_PENDING_OPS
        1
    }

    /// Given a logical address, returns an index into the batch at which it falls.
    #[inline(always)]
    pub(crate) fn index(&self, logical: usize) -> usize {
        // logical & (MAX_PENDING_OPS - 1)
        0
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// The Replica Node
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A token handed out to threads that replicas with replicas.
// #[derive(Copy, Clone, Eq, PartialEq)]
// pub struct ReplicaToken {
//     pub(crate) tid: ThreadIdx,
// }

pub type ReplicaToken = ThreadIdx;



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
    pub data: CachePadded<RwLock<NRState>>,


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
            &&& #[trigger] self.replicas[i].wf()
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
