use builtin_macros::verus_old_todo_no_ghost_blocks;


use crate::pervasive::prelude::*;
use crate::pervasive::cell::{PCell, PermissionOpt};
use crate::pervasive::map::Map;
use crate::pervasive::option::Option;
use crate::pervasive::vec::Vec;
use crate::pervasive::atomic_ghost::*;
use crate::pervasive::struct_with_invariants;

use crate::spec::cyclicbuffer::CyclicBuffer;
use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::types::*;
use crate::spec::unbounded_log::UnboundedLog;


use super::{LOG_SIZE, NUM_REPLICAS};

use super::cachepadded::CachePadded;

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

    //     invariant on alive with (cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits) {
    //         g@ === CyclicBuffer::token![ cyclic_buffer_instance => version_upper_bound => v as nat ]
    //     }
}

} // struct_with_invariants



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

}} // struct_with_invariants!{




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

} // verus_old_todo_no_ghost_blocks