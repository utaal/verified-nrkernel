// the verus dependencies
#[macro_use]
mod pervasive;
#[allow(unused_imports)] // XXX: should not be needed!
use pervasive::cell::{CellId, PCell, PermissionOpt};
#[allow(unused_imports)] // XXX: should not be needed!
use pervasive::map::Map;
use pervasive::option::Option;
use pervasive::prelude::*;
use pervasive::vec::Vec;
use pervasive::modes::{Gho, Trk, tracked_exec_borrow};

mod spec;
// mod exec;

use spec::cyclicbuffer::{CyclicBuffer, StoredType};
use spec::flat_combiner::FlatCombiner;
use spec::types::*;
use spec::unbounded_log::UnboundedLog;

use pervasive::atomic_ghost::*;

use crate::pervasive::struct_with_invariants;

verus_old_todo_no_ghost_blocks! {


/// the maximum number of replicas
pub const MAX_REPLICAS_PER_LOG: usize = 16;

/// the number of replicas we have
pub const NUM_REPLICAS: usize = 4;

/// the size of the log in bytes
pub const DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;

pub const LOG_SIZE: usize = 1024;

/// maximum number of threads per replica
pub const MAX_THREADS_PER_REPLICA: usize = 256;

pub const MAX_PENDING_OPS: usize = 1;

/// Constant required for garbage collection. When the tail and the head are these many
/// entries apart on the circular buffer, garbage collection will be performed by one of
/// the replicas registered with the log.
///
/// For the GC algorithm to work, we need to ensure that we can support the largest
/// possible append after deciding to perform GC. This largest possible append is when
/// every thread within a replica has a full batch of writes to be appended to the shared
/// log.
pub const GC_FROM_HEAD: usize = MAX_PENDING_OPS * MAX_THREADS_PER_REPLICA;


/// Threshold after how many iterations we abort and report the replica we're waiting for
/// as stuck for busy spinning loops.
///
/// Should be a power of two to avoid divisions.
pub const WARN_THRESHOLD: usize = 128;


pub const MAX_IDX : u64 = 0xffff_ffff_f000_0000;

/// a simpe cache padding for the struct fields
#[repr(align(128))]
pub struct CachePadded<T>(pub T);

/// Unique identifier for the given replica (relative to the log)
pub type ReplicaId = u32;

/// A (monotoically increasing) number that uniquely identifies a thread that's
/// registered with the replica.
pub type ThreadId = u32;

/// a token that identifies the replica
///
// #[derive(Copy, Clone, Eq, PartialEq)]
pub struct ReplicaToken {
    pub(crate) rid: ReplicaId,
}

impl ReplicaToken {
    // pub const fn new(rid: ReplicaId) -> Self {
    //     Self { rid }
    // }

    // pub const fn clone(&self) -> Self {
    //     Self { rid: self.rid }
    // }

    pub const fn id(&self) -> (result: ReplicaId)
        ensures result as nat == self.id_spec()
    {
        self.rid
    }

    pub open spec fn id_spec(&self) -> nat {
        self.rid as nat
    }
}


/// the thread token identifies a thread of a given replica
pub struct ThreadToken {
    /// the replica id this thread uses
    pub(crate) rid: ReplicaToken,
    /// identifies the thread within the replica
    pub(crate) tid: ThreadId,
}

impl ThreadToken {
    pub fn thread_id(&self) -> (result: ThreadId)
        ensures result as nat == self.thread_id_spec()
    {
        self.tid
    }

    pub open spec fn thread_id_spec(&self) -> nat {
        self.tid as nat
    }

    pub const fn replica_id(&self) -> (result: ReplicaId)
        ensures result as nat == self.replica_id_spec()
    {
        self.rid.id()
    }

    pub open spec fn replica_id_spec(&self) -> nat {
        self.rid.id_spec()
    }
}


#[verifier(external_body)] /* vattr */
pub fn print_starvation_warning(line: u32) {
    println!("WARNING({line}): has been looping for `WARN_THRESHOLD` iterations. Are we starving?");
}

#[verifier(external_body)] /* vattr */
pub fn panic_with_head_too_big() {
    panic!("WARNING: Head value exceeds the maximum value of u64.");
}

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

    pub log_entry: PCell<LogEntry>,

    /// Indicates whether this entry represents a valid operation when on the log.
    ///
    ///  - Dafny: linear alive: Atomic<bool, CBAliveBit>)
    ///  - Rust:  pub(crate) alivef: AtomicBool,
    pub alive: AtomicBool<_, CyclicBuffer::alive_bits, _>,

    /// the index into the cyclic buffer of this entry into the cyclig buffer.
    pub cyclic_buffer_idx: Ghost<nat>,

    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
}

pub open spec fn wf(&self) -> bool {
    invariant on alive with (cyclic_buffer_instance, cyclic_buffer_idx) is (v: bool, g: CyclicBuffer::alive_bits) {
        g@ === CyclicBuffer::token![ cyclic_buffer_instance@ => alive_bits => cyclic_buffer_idx@ => v ]
    }
}} // struct_with_invariants

impl BufferEntry {
    pub open spec fn inv(&self, perm: PermissionOpt<LogEntry>) -> bool {
        &&& self.log_entry.id() == perm@.pcell
    }
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
    /// The actual log, a slice of entries.
    ///  - Dafny: linear buffer: lseq<BufferEntry>,
    ///           glinear bufferContents: GhostAtomic<CBContents>,
    ///  - Rust:  pub(crate) slog: Box<[Cell<Entry<T, M>>]>,
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

    pub num_replicas: Ghost<nat>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
}

pub open spec fn wf(&self) -> bool {
    predicate {
        // XXX: not needed? && (forall nodeId | 0 <= nodeId < |node_info| :: nodeId in node_info)

        &&& self.num_replicas == NUM_REPLICAS

        // && |node_info| == NUM_REPLICAS as int
        &&& self.local_versions.len() == self.num_replicas

        // && |buffer| == LOG_SIZE as int
        &&& self.slog.len() == LOG_SIZE

        // && (forall i: nat | 0 <= i < LOG_SIZE as int :: buffer[i].WF(i, cb_loc_s))
        &&& (forall |i: nat| i < LOG_SIZE ==> #[trigger] self.slog[i as int].wf())

        // && (forall v, g :: atomic_inv(bufferContents, v, g) <==> ContentsInv(buffer, g, cb_loc_s))

        // make sure we
        &&& self.unbounded_log_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.num_replicas() == self.num_replicas
    }

    // invariant on slog with (

    invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound) {
        // && (forall v, g :: atomic_inv(ctail.inner, v, g) <==> g == Ctail(v as int))
        g@ === UnboundedLog::token![ unbounded_log_instance@ => version_upper_bound => v as nat ]
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head) {
        // && (forall v, g :: atomic_inv(head.inner, v, g) <==> g == CBHead(v as int, cb_loc_s))
        g@ === CyclicBuffer::token![ cyclic_buffer_instance@ => head => v as nat ]
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail, CyclicBuffer::tail)) {
        // && (forall v, g :: atomic_inv(globalTail.inner, v, g) <==> GlobalTailInv(v, g, cb_loc_s))
        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance@ => tail => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance@ => tail => v as nat ]
    }


    // && (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId, cb_loc_s))
    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_versions)) {


        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance@ => local_versions => i as nat => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance@ => local_versions => i as nat => v as nat ]
        &&& 0 <= v < MAX_IDX
    }
}
} // struct_with_invariants!{


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


    /// Returns a physical index given a logical index into the shared log.
    #[inline(always)]
    pub(crate) fn index(&self, logical: u64) -> (result: usize)
        requires
            self.slog.len() > 0
        ensures
            result as nat == self.index_spec(logical as nat),
            result < self.slog.len()
    {
        (logical as usize) % self.slog.len()
    }

    pub (crate) open spec fn index_spec(&self, logical: nat) -> nat
        recommends self.slog.len() > 0
    {
        logical % (self.slog.len() as nat)
    }

    #[inline(always)]
    pub(crate) fn is_alive_value(&self, logical: u64) -> (result: bool)
        requires
            self.slog.len() > 0
        ensures
            result == self.is_alive_value_spec(logical as nat)

    {
        assert(
            ((logical as usize) / self.slog.len()) as nat
                == ((logical as nat) / self.slog.len() as nat)
        )  by (nonlinear_arith);
        ((logical as usize) / self.slog.len() % 2) == 0
    }

    pub(crate) open spec fn is_alive_value_spec(&self, logical: nat) -> bool
        recommends self.slog.len() > 0
    {
        ((logical / (self.slog.len() as nat)) % 2) == 0
    }


    /// checks whether the version of the local replica has advanced enough to perform read operations
    ///
    /// This basically corresponds to the transition `readonly_read_to_read` in the unbounded log.
    ///
    // https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/log.rs#L525
    pub fn is_replica_synced_for_reads(&self, node_id: usize, version_upper_bound: u64,
                                       local_reads: Tracked<UnboundedLog::local_reads>)
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



    /// Inserts a slice of operations into the log.
    pub fn append(&self, ops: &Vec<UpdateOp>, rid: ReplicaToken,
        cb_combiner: Tracked<CyclicBuffer::combiner>
    )
        requires
            self.wf(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle(),
            cb_combiner@@.key == rid.id_spec()

    {
        let node_id = rid.id() as usize;

        // TODO!
        let nops = ops.len();

        let mut iteration = 1;
        let mut waitgc = 1;

        let tracked mut g_cb_comb_new = cb_combiner.get();

        while true
            invariant
                self.wf(),
                0 <= iteration <= WARN_THRESHOLD,
                g_cb_comb_new@.instance == self.cyclic_buffer_instance@,
                g_cb_comb_new@.key == node_id as nat,
                g_cb_comb_new@.value.is_Idle()
        {
            if iteration == WARN_THRESHOLD {
                print_starvation_warning(line!());
                return;
            }

            iteration = iteration + 1;

            // let tail = self.tail.load(Ordering::Relaxed);
            let tail = atomic_with_ghost!(
                &self.tail.0 => load();
                returning tail;
                ghost g => { }
            );

            // let head = self.head.load(Ordering::Relaxed);
            let head = atomic_with_ghost!(
                &self.head.0 => load();
                returning tail;
                ghost g => {
                    g_cb_comb_new = self.cyclic_buffer_instance
                        .borrow()
                        .advance_tail_start(node_id as nat, &g, g_cb_comb_new);
                }
            );

            // capture the warning here
            if head >= MAX_IDX {
                panic_with_head_too_big();
            }


            // If there are fewer than `GC_FROM_HEAD` entries on the log, then just
            // try again. The replica that reserved entry (h + self.slog.len() - GC_FROM_HEAD)
            // is currently trying to advance the head of the log. Keep refreshing the
            // replica against the log to make sure that it isn't deadlocking GC.
            // if tail > head + self.slog.len() - GC_FROM_HEAD  {  }
            if tail > head + ((self.slog.len() - GC_FROM_HEAD) as u64) {
                if waitgc == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    waitgc = 0;
                }

                proof {
                    g_cb_comb_new = self.cyclic_buffer_instance
                            .borrow()
                            .advance_tail_abort(node_id as nat, g_cb_comb_new);
                }

                // TODO:
                // self.execute(idx, &mut s);

                // self.advance_head(idx, &mut s)?;
                let rid_copy = ReplicaToken { rid: rid.rid };
                let adv_head_result = self.advance_head(rid_copy, tracked(g_cb_comb_new));
                g_cb_comb_new = adv_head_result.get();
                // XXX: that one here doesn't seem to work. `error: cannot call function with mode exec`
                // g_cb_comb_new = self.advance_head(rid_copy, tracked(g_cb_comb_new)).get();
                // continue;
            } else {
                let new_tail = tail + (nops as u64);

                // If on adding in the above entries there would be fewer than `GC_FROM_HEAD`
                // entries left on the log, then we need to advance the head of the log.
                let advance = new_tail > head + (self.slog.len() - GC_FROM_HEAD) as u64 ;

                // Try reserving slots for the operations. If that fails, then restart
                // from the beginning of this loop.
                // if self.tail.compare_exchange_weak(tail, tail + nops, Ordering::Acquire, Ordering::Acquire)

                let tracked adv_tail_finish_result : (
                    Gho<Map<int, StoredType>>,
                    Trk<Map<int, StoredType>>,
                    Trk<CyclicBuffer::combiner>,
                );


                let result = atomic_with_ghost!(
                    &self.tail.0 => compare_exchange(tail, new_tail);
                    update prev -> next;
                    returning result;
                    ghost g => {
                        if matches!(result, Result::Ok(tail)) {
                            let tracked (inf_tail, mut cb_tail) = g;

                            // place the updates in the log:
                            // self.unbouned_log_instance.borrow().update_place_ops_in_log_one()

                            adv_tail_finish_result = self.cyclic_buffer_instance.borrow()
                                .advance_tail_finish(node_id as nat, new_tail as nat, &mut cb_tail, g_cb_comb_new);

                            g_cb_comb_new = adv_tail_finish_result.2.0;
                            g = (inf_tail, cb_tail);

                        } else {
                            // no transition, abandon advance tail
                            g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                                    .advance_tail_abort(node_id as nat, g_cb_comb_new);
                        }
                    }
                );

                if matches!(result, Result::Ok(tail)) {

                }
            }
        }
    }


    /// Advances the head of the log forward. If a replica has stopped making
    /// progress, then this method will never return. Accepts a closure that is
    /// passed into execute() to ensure that this replica does not deadlock GC.
    pub fn advance_head(&self, rid: ReplicaToken,
        cb_combiner: Tracked<CyclicBuffer::combiner>)
         -> (result: Tracked<CyclicBuffer::combiner>)
        requires
            self.wf(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle()
        ensures
            result@@.instance == self.cyclic_buffer_instance@,
            result@@.value.is_Idle()
    {
        let tracked mut g_cb_comb_new = cb_combiner.get();
        let ghost g_node_id = cb_combiner@@.key;

        let mut iteration = 1;
        while true
            invariant
                self.wf(),
                g_cb_comb_new@.instance == self.cyclic_buffer_instance@,
                g_cb_comb_new@.value.is_Idle(),
                g_cb_comb_new@.key == g_node_id,
                0 <= iteration <= WARN_THRESHOLD
        {
            // TODO
            // let global_head = self.head.load(Ordering::Relaxed);
            let mut global_head = atomic_with_ghost!(
                &self.head.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );

            // let f = self.tail.load(Ordering::Relaxed);
            let mut global_tail = atomic_with_ghost!(
                &self.tail.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );

            let res = self.find_min_local_version(tracked(g_cb_comb_new));
            let min_local_version = res.0;
            g_cb_comb_new = res.1.get();

            // If we cannot advance the head further, then start
            // from the beginning of this loop again. Before doing so, try consuming
            // any new entries on the log to prevent deadlock.
            if min_local_version == global_head {
                g_cb_comb_new = self.cyclic_buffer_instance.borrow().advance_head_abort(g_node_id, g_cb_comb_new);

                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    return tracked(g_cb_comb_new);
                }
                iteration = iteration + 1;
            } else {
                // There are entries that can be freed up; update the head offset.
                // self.head.store(min_local_tail, Ordering::Relaxed);
                atomic_with_ghost!(
                    &self.head.0 => store(min_local_version);
                    update old_val -> new_val;
                    ghost g => {
                        g_cb_comb_new = self.cyclic_buffer_instance.borrow().advance_head_finish(g_node_id, &mut g, g_cb_comb_new);
                });

                if global_tail < min_local_version + (self.slog.len() - GC_FROM_HEAD) as u64 {
                    return tracked(g_cb_comb_new);
                }
            }
            // XXX: We don't have clone/copy, hmm...
            // let node_id_copy = ReplicaToken { rid: rid.rid };
            // g_cb_comb_new =  self.execute(node_id_copy);

        }
        tracked(g_cb_comb_new)
    }


    /// Executes a passed in closure (`d`) on all operations starting from a
    /// replica's local tail on the shared log. The replica is identified
    /// through an `idx` passed in as an argument.
    pub(crate) fn execute(&self, rid: ReplicaToken,
        local_updates: Tracked::<UnboundedLog::local_updates>,
        replica: Tracked<UnboundedLog::replicas>,
        combiner: Tracked<UnboundedLog::combiner>,
        cb_combiner: Tracked<CyclicBuffer::combiner>
    )
        requires
            self.wf(),
            rid.id_spec() < self.num_replicas@,
            replica@@.instance == self.unbounded_log_instance@,
            replica@@.key == rid.id_spec(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle(),
            cb_combiner@@.key == rid.id_spec(),
            combiner@@.value.is_Placed() || combiner@@.value.is_Ready(),
            combiner@@.key == rid.id_spec(),
            combiner@@.instance == self.unbounded_log_instance@

    {
        let node_id = rid.id() as usize;

        let tracked mut g_new_replica = replica.get();
        let tracked mut g_new_comb = combiner.get();
        let tracked mut g_new_cb_comb = cb_combiner.get();
        let tracked mut g_new_local_updates = local_updates.get();

        // if the combiner ins idle, we start it with the trival start transition
        proof {
            if combiner@@.value.is_Ready() {
                g_new_comb = self.unbounded_log_instance.borrow().exec_trivial_start(node_id as nat, g_new_comb);
            }
        }

        // let ltail = self.ltails[idx.0 - 1].load(Ordering::Relaxed);
        let mut local_version = atomic_with_ghost!(
            &self.local_versions.index(node_id).0 => load();
            returning ret;
            ghost g => {
                // this kicks of the state transition in both the cyclic buffer and the unbounded log
                g_new_comb = self.unbounded_log_instance.borrow().exec_load_local_version(node_id as nat, &g.0, g_new_comb);
                g_new_cb_comb = self.cyclic_buffer_instance.borrow().reader_start(node_id as nat, &g.1, g_new_cb_comb);
            });

        // Check if we have any work to do by comparing our local tail with the log's
        // global tail. If they're equal, then we're done here and can simply return.
        // let gtail = self.tail.load(Ordering::Relaxed);
        let global_tail = atomic_with_ghost!(
            &self.tail.0 => load();
            returning global_tail;
            ghost g => {
                if (local_version == global_tail) {
                    // there has ben no additional updates to be applied, combiner back to idle
                    g_new_comb = self.unbounded_log_instance.borrow().exec_finish_no_change(node_id as nat, &g.0, g_new_comb);
                    g_new_cb_comb = self.cyclic_buffer_instance.borrow().reader_abort(node_id as nat, g_new_cb_comb);
                } else {
                    g_new_comb = self.unbounded_log_instance.borrow().exec_load_global_head(node_id as nat, &g.0, g_new_comb);
                    g_new_cb_comb = self.cyclic_buffer_instance.borrow().reader_enter(node_id as nat,  &g.1, g_new_cb_comb);
                }
            });

        // Execute all operations from the passed in offset to the shared log's tail.
        // Check if the entry is live first; we could have a replica that has reserved
        // entries, but not filled them into the log yet.
        // for i in ltail..gtail {
        while local_version < global_tail
            invariant
                self.wf()
        {
            let mut iteration = 1;

            let actual_idx = self.index(local_version);
            let is_alive_value = self.is_alive_value(local_version);

            let mut is_alive = false;
            while !is_alive
                invariant
                    self.wf(),
                    actual_idx < self.slog.len(),
                    0 <= iteration <= WARN_THRESHOLD,
                    self.slog.spec_index(actual_idx as int).wf()
            {
                let tracked reader_guard_result : (Gho<Map<int, StoredType>>,Trk<CyclicBuffer::combiner>);
                let alive_bit = atomic_with_ghost!(
                    &self.slog.index(actual_idx).alive => load();
                    returning alive_bit;
                    ghost g => {
                        if alive_bit == is_alive_value {
                            reader_guard_result = self.cyclic_buffer_instance.borrow().reader_guard(node_id as nat, &g, g_new_cb_comb);
                            g_new_cb_comb = reader_guard_result.1.0;
                        }
                    });

                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    iteration = 0;
                }

                is_alive = alive_bit == is_alive_value;
                iteration = iteration + 1;
            }

            // now we know the entry is alive

            let tracked stored_entry : &StoredType;
            proof {
                stored_entry = self.cyclic_buffer_instance.borrow().guard_guards(node_id as nat, &g_new_cb_comb);
            }

            // read the entry
            let log_entry = self.slog.index(actual_idx).log_entry.borrow(tracked_exec_borrow(&stored_entry.cell_perms));

            // actual_replica', ret := nrifc.do_update(actual_replica', log_entry.op);

            proof {
                if log_entry.node_id == node_id as nat {
                    self.unbounded_log_instance.borrow().pre_exec_dispatch_local(node_id as nat, &stored_entry.log_entry, &g_new_comb);

                    let tracked exec_dispatch_result = self.unbounded_log_instance.borrow()
                        .exec_dispatch_local(node_id as nat, &stored_entry.log_entry, g_new_replica, g_new_local_updates, g_new_comb);

                    g_new_replica = exec_dispatch_result.0.0;
                    g_new_local_updates = exec_dispatch_result.1.0;
                    g_new_comb = exec_dispatch_result.2.0;

                } else {
                    // unbounded_log::log

                    // param_token_2_log:&log,
                    // param_token_1_replicas: replicas,
                    let tracked exec_dispatch_result = self.unbounded_log_instance.borrow().exec_dispatch_remote(node_id as nat, &stored_entry.log_entry, g_new_replica, g_new_comb);
                    g_new_replica = exec_dispatch_result.0.0;
                    g_new_comb = exec_dispatch_result.1.0;
                }

                // unguard
                g_new_cb_comb = self.cyclic_buffer_instance.borrow().reader_unguard(node_id as nat, g_new_cb_comb);
            }

            local_version = local_version + 1;
        }




        //
        //     let e = self.slog[self.index(i)].as_ptr();

        //     while unsafe { (*e).alivef.load(Ordering::Acquire) != self.lmasks[idx.0 - 1].get() } {
        //         if iteration % WARN_THRESHOLD == 0 {
        //             warn!(
        //                 "alivef not being set for self.index(i={}) = {} (self.lmasks[{}] is {})...",
        //                 i,
        //                 self.index(i),
        //                 idx.0 - 1,
        //                 self.lmasks[idx.0 - 1].get()
        //             );
        //         }
        //         iteration += 1;
        //     }

        //     unsafe {
        //         d(
        //             (*e).operation.as_ref().unwrap().clone(),
        //             (*e).replica == idx.0,
        //         )
        //     };

        //     // Looks like we're going to wrap around now; flip this replica's local mask.
        //     if self.index(i) == self.slog.len() - 1 {
        //         self.lmasks[idx.0 - 1].set(!self.lmasks[idx.0 - 1].get());
        //         //trace!("idx: {} lmask: {}", idx, self.lmasks[idx - 1].get());
        //     }
        // }

        // // Update the completed tail after we've executed these operations. Also update
        // // this replica's local tail.
        // self.ctail.fetch_max(gtail, Ordering::Relaxed);
        // self.ltails[idx.0 - 1].store(gtail, Ordering::Relaxed);

    }


    /// Loops over all `local_versions` and finds the replica with the lowest version.
    ///
    /// # Returns
    /// The ID (in `LogToken`) of the replica with the lowest tail and the
    /// corresponding/lowest tail `idx` in the `Log`.
    ///
    ///  - Dafny: part of advance_head
    pub(crate) fn find_min_local_version(&self, cb_combiner: Tracked<CyclicBuffer::combiner>)
                        -> (result: (u64, Tracked<CyclicBuffer::combiner>))
        requires
            self.wf(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle()
        ensures
            result.0 < MAX_IDX,
            result.1@@.key == cb_combiner@@.key,
            result.1@@.value.is_AdvancingHead(),
            result.1@@.instance == self.cyclic_buffer_instance@,
            result.1@@.value.get_AdvancingHead_idx() == self.num_replicas,
            result.1@@.value.get_AdvancingHead_min_local_version() == result.0
    {
        // let r = self.next.load(Ordering::Relaxed);
        let num_replicas = self.local_versions.len();

        let tracked mut g_cb_comb_new : CyclicBuffer::combiner = cb_combiner.get();
        let ghost g_node_id = cb_combiner@@.key;

        // let (mut min_replica_idx, mut min_local_tail) = (0, self.ltails[0].load(Ordering::Relaxed));
        let mut min_local_version = atomic_with_ghost!(
            &self.local_versions.index(0).0 => load();
            returning ret;
            ghost g => {
                // do the transition
                g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                        .advance_head_start(g_node_id, &g.1, g_cb_comb_new);
            });

        // Find the smallest local tail across all replicas.
        // for idx in 1..r {
        //    let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
        //    min_local_tail = min(min_local_tail, cur_local_tail)
        //}
        let mut idx : usize = 1;
        while idx < num_replicas
            invariant
                self.wf(),
                0 <= idx <= num_replicas,
                min_local_version < MAX_IDX,
                g_cb_comb_new@.instance == self.cyclic_buffer_instance,
                g_cb_comb_new@.value.is_AdvancingHead(),
                g_cb_comb_new@.value.get_AdvancingHead_idx() == idx,
                g_cb_comb_new@.value.get_AdvancingHead_min_local_version() == min_local_version,
                g_cb_comb_new.view().key == g_node_id,
                num_replicas == self.local_versions.len()
        {
            assert(num_replicas == self.local_versions.len());
            assert(idx < self.local_versions.len());

            // let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
            let cur_local_tail = atomic_with_ghost!(
                &self.local_versions.index(idx).0 => load();
                returning ret;
                ghost g => {
                    // do the transition
                    g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                            .advance_head_next(g_node_id, &g.1, g_cb_comb_new);
                });
            if cur_local_tail < min_local_version {
                min_local_version = cur_local_tail;
            }

            idx = idx + 1;
        }
        (min_local_version, tracked(g_cb_comb_new))
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

impl<D> RwLock<D> {
    pub open spec fn internal_inv(&self) -> bool {
        true
    }

    pub open spec fn inv(&self) -> bool {
        true
    }
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
/// The ghost context for a thread carying permissions and tracking the state of the update operation
///
///  - Dafny:   glinear datatype ContextGhost = ContextGhost(
pub tracked struct ContextGhost {
    /// Token to access the batch cell in Context
    ///
    ///  - Dafny: glinear contents: glOption<CellContents<OpResponse>>,
    pub batch_token: Tracked<PermissionOpt<PendingOperation>>,

    /// The flat combiner slot.
    /// XXX: somehow can't make this tracked?
    ///
    ///  - Dafny: glinear fc: FCSlot,
    pub slots: FlatCombiner::slots,

    /// tracks the update operation
    ///
    ///  - Dafny: glinear update: glOption<Update>
    pub update: Tracked<Option<UnboundedLog::local_updates>>
}

//  - Dafny: predicate inv(v: uint64, i: nat, cell: Cell<OpResponse>, fc_loc_s: nat)
pub open spec fn inv(&self, v: u64, tid: nat, cell: PCell<PendingOperation>, fc: FlatCombiner::Instance) -> bool {
    predicate {
        // // && fc.tid == i
        &&& self.slots@.key == tid

        // && fc.loc_s == fc_loc_s
        &&& self.slots@.instance == fc

        // && (v == 0 || v == 1)
        &&& ((v == 0) || (v == 1))

        // && (v == 0 ==> fc.state.FCEmpty? || fc.state.FCResponse?)
        &&& (v == 0 ==> self.slots@.value.is_Empty() || self.slots@.value.is_Response())

        // && (v == 1 ==> fc.state.FCRequest? || fc.state.FCInProgress?)
        &&& (v == 1 ==> self.slots@.value.is_Request() || self.slots@.value.is_InProgress())

        // && (fc.state.FCEmpty? ==>
        //   && update.glNone?
        //   && contents.glNone?
        // )
        &&& (self.slots@.value.is_Empty() ==> {
            &&& self.update@.is_None()
            &&& self.batch_token@@.value.is_None()
        })

        // && (fc.state.FCRequest? ==>
        //   && update.glSome?
        //   && update.value.us.UpdateInit?
        //   && update.value.rid == fc.state.rid
        //   && contents.glSome?
        //   && contents.value.cell == cell
        //   && contents.value.v.op == update.value.us.op
        // )
        &&& (self.slots@.value.is_Request() ==> {
            &&& self.update@.is_Some()
            &&& self.update@.get_Some_0()@.value.is_Init()
            &&& self.update@.get_Some_0()@.key == self.slots@.value.get_ReqId()

            &&& self.batch_token@@.value.is_Some()
            &&& self.batch_token@@.pcell == cell.id()
            &&& self.batch_token@@.value.get_Some_0().op.is_Some()
            &&& self.batch_token@@.value.get_Some_0().op.get_Some_0() == self.update@.get_Some_0()@.value.get_Init_op()
        })

        // && (fc.state.FCInProgress? ==>
        //   && update.glNone?
        //   && contents.glNone?
        // )
        &&& (self.slots@.value.is_InProgress() ==> {
            &&& self.update@.is_None()
            &&& self.batch_token@@.value.is_None()
        })

        // && (fc.state.FCResponse? ==>
        //   && update.glSome?
        //   && update.value.us.UpdateDone?
        //   && update.value.rid == fc.state.rid
        //   && contents.glSome?
        //   && contents.value.cell == cell
        //   && contents.value.v.ret == update.value.us.ret
        // )
        &&& (self.slots@.value.is_InProgress() ==> {
            &&& self.update@.is_Some()
            &&& self.update@.get_Some_0()@.value.is_Done()
            &&& self.update@.get_Some_0()@.key == self.slots@.value.get_ReqId()

            &&& self.batch_token@@.value.is_Some()
            &&& self.batch_token@@.pcell == cell.id()
            &&& self.batch_token@@.value.get_Some_0().resp.get_Some_0() == self.update@.get_Some_0()@.value.get_Done_ret()
        })
    }
}
} // struct_with_invariants! ContextGhost


struct_with_invariants!{
/// Contains state of a particular thread context within NR w.r.g. to outstanding operations.
///
///  - Dafny: linear datatype Context = Context(
///  - Rust:  pub(crate) struct Context<T, R, M>
///
/// Note, in contrast to the Rust version, we just have a single outstanding operation
#[repr(align(128))]
pub struct Context {
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    ///
    /// This is protected by the `atomic` field.
    ///
    ///  - Dafny: linear cell: CachePadded<Cell<OpResponse>>
    ///  - Rust:  pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],
    pub (crate) batch: CachePadded<PCell<PendingOperation>>,

    /// The number of operations in this context, (just 0 or 1)
    ///
    ///  - Dafny: linear atomic: CachePadded<Atomic<uint64, ContextGhost>>,
    ///  - Rust:  N/A
    pub (crate) atomic: CachePadded<AtomicU64<_, ContextGhost, _>>,

    /// ghost: identifier of the thread
    pub thread_id_g: Tracked<ThreadToken>,

    /// ghost: the flat combiner instance
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

// XXX: in Dafny, this predicate takes the thread id and the flat combiner instance as arguments,
// but it seems that this is not possible here?
pub open spec fn wf(&self) -> bool {
    invariant on atomic with (flat_combiner_instance, batch, thread_id_g) specifically (self.atomic.0) is (v: u64, g: ContextGhost) {
        // (forall v, g :: atomic_inv(atomic.inner, v, g) <==> g.inv(v, i, cell.inner, fc_loc))
        &&& g.inv(v, thread_id_g@.thread_id_spec(), batch.0, flat_combiner_instance@)
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



// TODO: add the ThreadOwnedContext here!


////////////////////////////////////////////////////////////////////////////////////////////////////
// Replicated Data Structure
////////////////////////////////////////////////////////////////////////////////////////////////////

struct_with_invariants!{
// linear datatype NodeReplica = NodeReplica(
pub struct ReplicatedDataStructure {
    /// the actual data structure
    ///  - Dafny: linear actual_replica: nrifc.DataStructureType,
    pub data: NRState,
    // TODO: add the ghost replica here!
    ///  - Dafny: glinear ghost_replica: Replica,
    ///  - Dafny: glinear combiner: CombinerToken,
    pub combiner: Tracked<UnboundedLog::combiner>,
    ///  - Dafny: glinear cb: CBCombinerToken
    pub cb_combiner: Tracked<CyclicBuffer::combiner>
}

//  - Dafny: predicate WF(nodeId: nat, cb_loc_s: nat) {
pub open spec fn wf(&self, node_id: nat, cb: CyclicBuffer::Instance) -> bool {
    predicate {
        // && ghost_replica.state == nrifc.I(actual_replica)
        // && ghost_replica.nodeId == nodeId
        // && combiner.state == CombinerReady
        &&& self.combiner@@.value.is_Ready()
        // && combiner.nodeId == nodeId
        &&& self.combiner@@.key == node_id
        // && cb.nodeId == nodeId
        &&& self.cb_combiner@@.key == node_id
        // && cb.rs.CombinerIdle?
        &&& self.cb_combiner@@.value.is_Idle()
        // && cb.cb_loc_s == cb_loc_s
        &&& self.cb_combiner@@.instance == cb
    }
}} // struct_with_invariants

////////////////////////////////////////////////////////////////////////////////////////////////////
// The Replica Node
////////////////////////////////////////////////////////////////////////////////////////////////////


struct_with_invariants!{
/// Ghost state that is protected by the combiner lock
///
///  - Dafny: glinear datatype CombinerLockState
///  - Rust:  N/A
pub tracked struct CombinerLockStateGhost {
    // glinear flatCombiner: FCCombiner,
    pub combiner: Tracked<FlatCombiner::combiner>,

    /// Stores the token to access the op_buffer in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    pub op_buffer_token: Tracked<PermissionOpt<Vec<UpdateOp>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    pub responses_token: Tracked<PermissionOpt<Vec<ReturnType>>>,
}

//  - Dafny: predicate CombinerLockInv(v: uint64, g: glOption<CombinerLockState>, fc_loc: nat,
//                                     ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
//                                     responses: LC.LinearCell<seq<nrifc.ReturnType>>)
//
// Note: this predicate only holds when the lock is not taken.
pub open spec fn inv(&self, combiner_instance: FlatCombiner::Instance, responses_id: CellId, op_buffer_id: CellId) -> bool {
    predicate {
        // && g.value.flatCombiner.state == FC.FCCombinerCollecting([])
        &&& self.combiner@@.value.is_Collecting()
        &&& self.combiner@@.value.get_Collecting_0().len() == 0

        // && g.value.flatCombiner.loc_s == fc_loc
        &&& self.combiner@@.instance == combiner_instance

        // && g.value.gops.v.Some?
        &&& self.op_buffer_token@@.value.is_Some()

        // && g.value.gresponses.lcell == responses
        &&& self.op_buffer_token@@.pcell == op_buffer_id

        // && |g.value.gops.v.value| == MAX_THREADS_PER_REPLICA as int
        &&& self.op_buffer_token@@.value.get_Some_0().len() == MAX_THREADS_PER_REPLICA

        // && g.value.gresponses.v.Some?
        &&& self.responses_token@@.value.is_Some()

        // && g.value.gops.lcell == ops
        &&& self.responses_token@@.pcell == responses_id

        // && |g.value.gresponses.v.value| == MAX_THREADS_PER_REPLICA as int
        &&& self.responses_token@@.value.get_Some_0().len() == MAX_THREADS_PER_REPLICA
    }
}} // struct_with_invariants!





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
    pub replica_token: ReplicaToken,

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


    /// Thread index that will be handed out to the next thread that registers
    // with the replica when calling [`Replica::register()`].
    // next: CachePadded<AtomicU64<_, FlatCombiner::num_threads, _>>,

    // /// Number of operations collected by the combiner from each thread at any
    // we just have one inflight operation per thread
    // inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

pub open spec fn wf(&self) -> bool {

    predicate {
        // && (forall i | 0 <= i < |contexts| :: i in contexts && contexts[i].WF(i, fc_loc))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> #[trigger] self.contexts[i as int].wf())
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> #[trigger] self.contexts[i as int].get_thread_id() == i)
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> #[trigger] self.contexts[i as int].flat_combiner_instance == self.flat_combiner_instance)

        // && |contexts| == MAX_THREADS_PER_REPLICA as int
        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        // && 0 <= nodeId as int < NUM_REPLICAS as int
        &&& 0 <= self.replica_token.rid < NUM_REPLICAS
        // && replica.InternalInv()
        &&& self.data.0.internal_inv()

        // XXX: What is that one here???
        // seems to refer to module NodeReplica(nrifc: NRIfc) refines ContentsTypeMod
        // of the actual replica wrapping the data structure?
        //&& (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int, nr.cb_loc_s))
    }

    // (forall v, g :: atomic_inv(combiner_lock.inner, v, g) <==> CombinerLockInv(v, g, fc_loc, ops, responses))
    invariant on combiner with (flat_combiner_instance, responses, op_buffer) specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost>) {
        // v != means lock is not taken,
        &&& (v == 0) <==> g.is_Some()
        // the lock is not taken, the ghost state is Some
        &&& (g.is_Some() ==> g.get_Some_0().inv(flat_combiner_instance@, responses.id(), op_buffer.id()))
    }

    // invariant on next specifically (self.next.0) is (v: u64, g: FlatCombiner::num_threads) {
    //     &&& 0 <= v < MAX_THREADS_PER_REPLICA
    //     &&& v == g
    // }
}

} // struct_with_invariants!


// macro_rules! myatomic_with_ghost_no_op {
//     ($e:expr, $g:ident, $b:block) => {
//         ::builtin_macros::verus_exec_expr!{ {
//             let atomic = &($e);
//             crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
//                 #[allow(unused_mut)]
//                 #[verifier::proof] let (perm, mut $g) = pair;

//                 proof { $b }

//                 pair = (perm, $g);
//             });
//         } }
//     }
// }

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
        //   result.0 ==> self.combiner.0.atomic_inv.constant().1 != 0
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
                    lock_g = tracked(g);    // obtain the protected lock state
                    assert(next == 2);

                    g = Option::None;       // we took the lock, set the ghost state to None,
                } else {
                    lock_g = tracked(None); // the lock was already taken, set it to None
                }
            }
        );

        if let Result::Ok(val) = res {
            assert(lock_g.is_Some());
            assert(val == 0);
            (val == 0, tracked(lock_g))
        } else {
            (false, tracked(None))
        }
    }

    fn release_combiner_lock(&self, tracked lock_state: Tracked<CombinerLockStateGhost>)
        requires
            self.wf(),
            lock_state@.inv(self.flat_combiner_instance@, self.responses.id(), self.op_buffer.id()),
            // self.combiner.0.atomic_inv.constant().1 != 0
            // lock_state@.combiner@@.value.is_Collecting(),
            // lock_state@.combiner@@.value.get_Collecting_0().len() == 0,
    {
        atomic_with_ghost!(
            &self.combiner.0 => store(0);
            update old_val -> new_val;
            ghost g
            => {
                // assert(old_val == v);
                assume(old_val != 0);
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
            assume(false);
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
        // let n_contexts = self.contexts.len();
        // let mut thread_idx = 0;
        // while thread_idx < n_contexts {
        //     let res = atomic_with_ghost!(
        //         &self.contexts.index(0).atomic.0 => load();
        //         returning ret;
        //         ghost g // g : ContextGhost
        //     => {
        //         // nothing in the buffer here
        //         if ret == 0 {
        //             self.flat_combiner_instance.borrow().combiner_collect_empty(&g.slots, flat_combiner_mut.borrow_mut());
        //         } else {
        //             g.slots = self.flat_combiner_instance.borrow().combiner_collect_request(g.slots, flat_combiner_mut.borrow_mut());
        //         }
        //     });

        //     thread_idx =  thread_idx + 1;
        // }

        //     let ctxt_iter = self.contexts[i - 1].iter();
        //     operations[i - 1] = ctxt_iter.len();
        //     // meta-data is (), throw it away
        //     buffer.extend(ctxt_iter.map(|op| op.0));
        // }


        // self.flat_combiner_instance.borrow().combiner_responding_start(flat_combiner_mut.borrow_mut());

        // (tracked(flat_combiner))
        assume(false);
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
        // assert(false);
        None
    }

    /// Executes an immutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute(&self, slog: &NrLog, op: ReadonlyOp, idx: ThreadToken) -> Result<ReturnType, () /* ReplicaError */>
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

        // assert(false);
        Err(())
    }

    /// Executes a mutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute_mut(&self, slog: &NrLog, op: UpdateOp, idx: ThreadToken) -> Result<ReturnType, () /* ReplicaError */>
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
        // assert(false);
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
    pub (crate) log: NrLog,
    // log: NrLog,

    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<NRState, UpdateOp, ReturnType>>>,
    pub (crate) replicas: Vec<Box<Replica>>,

    /// something that creates new request ids, or do we
    // #[verifier::proof] request_id: ReqId,

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
}



/// Proof blocks for the NodeReplicate data structure
impl NodeReplicated {
    pub open spec fn wf(&self) -> bool {
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
        // assert(false);
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
          self.wf(),
          forall |i| 0 <= i < self.replicas.len() ==> #[trigger] self.replicas[i].wf()
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            self.replicas.index(replica_id).execute_mut(&self.log, op, tkn)
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
        requires
            self.wf(),
            forall |i| 0 <= i < self.replicas.len() ==> #[trigger] self.replicas[i].wf()
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id< self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            self.replicas.index(replica_id).execute(&self.log, op, tkn)
        } else {
            Err(())
        }
    }
}


} // verus!

pub fn main() {}
