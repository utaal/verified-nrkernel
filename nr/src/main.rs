// the verus dependencies
#[macro_use]
mod pervasive;

#[allow(unused_imports)] // XXX: should not be needed!
use pervasive::{
    cell::{CellId, PCell, PermissionOpt},
    map::Map,
    modes::{tracked_exec_borrow, tracked_exec, ghost_exec, Gho, Trk},
    option::Option,
    prelude::*,
    vec::Vec,
    atomic_ghost::*,
    struct_with_invariants,
};

// use pervasive::slice::slice_index_set;

mod spec;
// mod exec;
// #[macro_use]
// mod rwlock;
#[allow(unused_imports)]
use spec::{
    cyclicbuffer::{CyclicBuffer, StoredType, stored_type_inv, LogicalLogIdx},
    flat_combiner::FlatCombiner,
    types::*,
    unbounded_log::UnboundedLog,
    rwlock::{RwLockSpec},
};

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

/// the maximum number of requests
pub const MAX_REQUESTS: usize = MAX_THREADS_PER_REPLICA * MAX_PENDING_OPS;

/// interval when we do a try_combine when checking for responses
pub const RESPONSE_CHECK_INTERVAL : usize = 0x1000_0000;

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




#[verifier(external_body)] /* vattr */
pub fn print_starvation_warning(line: u32) {
    println!("WARNING({line}): has been looping for `WARN_THRESHOLD` iterations. Are we starving?");
}

#[verifier(external_body)] /* vattr */
pub fn panic_with_tail_too_big() {
    panic!("WARNING: Tail value exceeds the maximum value of u64.");
}

#[verifier(external_body)] /* vattr */
pub fn spin_loop_hint() {
    core::hint::spin_loop();
}

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


/// the thread token identifies a thread of a given replica
///
///  - Dafny: linear datatype ThreadOwnedContext
pub struct ThreadToken {
    /// the replica id this thread uses
    pub(crate) rid: ReplicaToken,
    /// identifies the thread within the replica
    pub(crate) tid: ThreadId,
    /// the flat combiner client of the thread
    pub fc_client: Tracked<FlatCombiner::clients>,
    /// the permission to access the thread's operation batch
    pub batch_perm: Tracked<PermissionOpt<PendingOperation>>,
}

impl ThreadToken {
    pub open spec fn wf(&self) -> bool
    {
        &&& self.rid.wf()
        &&& self.fc_client@@.value.is_Idle()
        &&& (self.tid as nat) < MAX_THREADS_PER_REPLICA
        // &&& self.fc_client@@.instance == fc_inst
        &&& self.batch_perm@@.value.is_None()
        &&& self.fc_client@@.key == self.tid as nat
    }

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

pub open spec fn rids_match(
    bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat) -> bool
    decreases bools_end - bools_start
        when 0 <= bools_start <= bools_end <= bools.len() && 0 <= rids_start <= rids_end <= rids.len()
{

    if bools_end == bools_start {
      rids_end == rids_start
    } else {
      if bools[bools_end - 1].is_Some() {
        &&& rids_end > rids_start
        &&& rids[rids_end - 1] == bools[bools_end - 1].get_Some_0()
        &&& rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat)
      } else {
        rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end)
      }
    }
}

proof fn rids_match_add_none(bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
    ensures
        rids_match(bools.push(Option::None), rids, bools_start, bools_end, rids_start, rids_end)
    decreases bools_end - bools_start
{
    let bools_new = bools.push(Option::None);
    if bools_end == bools_start {
        assert(rids_match(bools_new, rids, bools_start, bools_end, rids_start, rids_end));
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_add_none(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat);
        } else {
            rids_match_add_none(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end);
        }
    }
}

proof fn rids_match_add_rid(bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat, rid: ReqId)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
    ensures
        rids_match(bools.push(Option::Some(rid)), rids.push(rid), bools_start, bools_end, rids_start, rids_end)
    decreases bools_end - bools_start
{
    let bools_new = bools.push(Option::Some(rid));
    let rids_new = rids.push(rid);
    if bools_end == bools_start {
        assert(rids_match(bools_new, rids_new, bools_start, bools_end, rids_start, rids_end));
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_add_rid(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat, rid);
        } else {
            rids_match_add_rid(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end, rid);
        }
    }
}

proof fn rids_match_pop(
    bools: Seq<Option<ReqId>>, rids: Seq<ReqId>,
    bools_start: nat, bools_end: nat, rids_start: nat, rids_end: nat)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
    ensures
        bools_end == bools_start ==> {
            rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
        },
        bools_end > bools_start ==> {
            &&& bools[bools_start as int].is_Some() ==> {
                &&& rids_start < rids_end
                &&& rids[rids_start as int] == bools[bools_start as int].get_Some_0()
                &&& rids_match(bools, rids, (bools_start + 1) as nat, bools_end, (rids_start + 1) as nat, rids_end)
            }
            &&& bools[bools_start as int].is_None() ==> {
                &&& rids_match(bools, rids, (bools_start + 1) as nat, bools_end, rids_start, rids_end)
            }
        }
    decreases bools_end - bools_start

{
    if bools_end == bools_start {
    } else {
      if bools[bools_end - 1].is_Some() {
        rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat);
        // if bools_end - 1 > bools_start {
        //   rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, (rids_end - 1) as nat);
        // }
      } else {
        rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end);
        // if bools_end - 1 > bools_start {
        //   rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end);
        // }
      }
    }
}



////////////////////////////////////////////////////////////////////////////////////////////////////
// NR Log
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Data structure that is passed between the append and exec functins of the log.
pub tracked struct NrLogAppendExecDataGhost {
    pub(crate) local_updates: Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
    pub(crate) ghost_replica: Tracked<UnboundedLog::replicas>,
    pub(crate) combiner: Tracked<UnboundedLog::combiner>,
    pub(crate) cb_combiner: Tracked<CyclicBuffer::combiner>,
    pub(crate) request_ids: Ghost<Seq<ReqId>>,
}

impl NrLogAppendExecDataGhost {
    pub open spec fn append_pre(&self, ops: Seq<UpdateOp>,  nid: NodeId, inst: UnboundedLog::Instance, cb_inst: CyclicBuffer::Instance) -> bool {

        // XXX: a maximum number of requests so there's no overflow
        &&& self.request_ids@.len() <= MAX_REQUESTS

        // requires nr.cb_loc_s == cb.cb_loc_s
        &&& self.cb_combiner@@.instance == cb_inst
        // requires cb.nodeId == node.nodeId as int
        &&& self.cb_combiner@@.key == nid
        // requires cb.rs.CombinerIdle?
        &&& self.cb_combiner@@.value.is_Idle()
        // requires combinerState.nodeId == node.nodeId as int
        &&& self.combiner@@.key == nid
        // requires combinerState.state == CombinerReady
        &&& self.combiner@@.value.is_Ready()

        &&& self.combiner@@.instance == inst
        // same number of ops as request ids
        &&& self.request_ids@.len() == ops.len()
        // requires forall i | 0 <= i < |requestIds| ::
        //     i in updates && updates[i] == Update(requestIds[i], UpdateInit(ops[i]))
        &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
        &&& (forall |i| #![trigger self.local_updates@[i]] 0 <= i < self.request_ids@.len() ==> {
            &&& #[trigger] self.local_updates@.contains_key(i)
            &&& self.local_updates@[i]@.instance == inst
            &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
            &&& self.local_updates@[i]@.value.is_Init()
            &&& self.local_updates@[i]@.value.get_Init_op() == ops[i as int]
        })

        // requires |ops| == MAX_THREADS_PER_REPLICA as int
        // requires |requestIds| == num_ops as int <= MAX_THREADS_PER_REPLICA as int
        // requires |requestIds| <= MAX_THREADS_PER_REPLICA as int
        // requires |responses| == MAX_THREADS_PER_REPLICA as int

        // requires ghost_replica.nodeId == node.nodeId as int
        &&& self.ghost_replica@@.key == nid
        &&& self.ghost_replica@@.instance == inst
        // &&& self.ghost_replica@@.value == actual_replica.I_();
        // requires ghost_replica.state == nrifc.I(actual_replica)
    }

    pub open spec fn append_post(&self, nid: NodeId, inst: UnboundedLog::Instance, cb_inst: CyclicBuffer::Instance, operations: Seq<UpdateOp>, responses: Seq<ReturnType>) -> bool {

        // XXX: a maximum number of requests so there's no overflow
        &&& self.request_ids@.len() <= MAX_REQUESTS

        // same number of ops as request ids
        &&& self.request_ids@.len() == operations.len()

        // ensures combinerState'.state.CombinerReady? || combinerState'.state.CombinerPlaced?
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.instance == inst
        &&& self.combiner@@.key == nid

        // TODO: ensures combinerState'.state.CombinerReady? ==> post_exec(node, requestIds, responses', updates', combinerState')
        &&& self.combiner@@.value.is_Ready() ==> {
            &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
            &&& (forall |i| #![trigger self.local_updates@[i]] 0 <= i < self.request_ids@.len() ==> {
                &&& #[trigger] self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.instance == inst
                &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
                &&& self.local_updates@[i]@.value.is_Done()
                &&& self.local_updates@[i]@.value.get_Done_ret() == responses[i as int]
            })
        }
        // TODO: ensures combinerState'.state.CombinerPlaced? ==> pre_exec(node, requestIds, responses', updates', combinerState')
        &&& self.combiner@@.value.is_Placed() ==> {
            &&& self.combiner@@.value.get_Placed_queued_ops() == self.request_ids@
            &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
            &&& (forall |i| #![trigger self.local_updates@[i]]  0 <= i < self.request_ids@.len() ==> {
                &&& #[trigger] self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.instance == inst
                &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
                &&& self.local_updates@[i]@.value.is_Placed()
                //TODO: self.local_updates[i]@.value.get_Placed_idx() == self.request_ids
            })
        }
        // ensures cb' == cb,
        // &&& self.cb_combiner@@ == pre.cb_combiner@@

        // requires nr.cb_loc_s == cb.cb_loc_s
        &&& self.cb_combiner@@.instance == cb_inst
        // requires cb.nodeId == node.nodeId as int
        &&& self.cb_combiner@@.key == nid
        // requires cb.rs.CombinerIdle?
        &&& self.cb_combiner@@.value.is_Idle()

        // ensures ghost_replica'.nodeId == node.nodeId as int
        &&& self.ghost_replica@@.key == nid
        &&& self.ghost_replica@@.instance == inst
        // TODO: ensures ghost_replica'.state == nrifc.I(actual_replica')
    }

    pub open spec fn execute_pre(&self, nid: NodeId, inst: UnboundedLog::Instance, cb_inst: CyclicBuffer::Instance) -> bool {
        // requires nr.cb_loc_s == cb.cb_loc_s
        &&& self.cb_combiner@@.instance == cb_inst
        // requires cb.nodeId == node.nodeId as int
        &&& self.cb_combiner@@.key == nid
        // requires cb.rs.CombinerIdle?
        &&& self.cb_combiner@@.value.is_Idle()

        // XXX: a maximum number of requests so there's no overflow
        &&& self.request_ids@.len() <= MAX_REQUESTS

        // requires combinerState.state.CombinerReady? || combinerState.state.CombinerPlaced?
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        // requires combinerState.nodeId == node.nodeId as int
        &&& self.combiner@@.key == nid
        &&& self.combiner@@.instance == inst

        // TODO:requires combinerState.state.CombinerPlaced? ==> pre_exec(node, requestIds, responses, updates, combinerState)
        &&& self.combiner@@.value.is_Placed() ==> {
            &&& self.combiner@@.value.get_Placed_queued_ops() == self.request_ids@
            &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
            &&& (forall |i| #![trigger self.local_updates@[i]] 0 <= i < self.request_ids@.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.instance == inst
                &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
                &&& self.local_updates@[i]@.value.is_Placed()
                //TODO: self.local_updates[i]@.value.get_Placed_idx() == self.request_ids
            })
        }

        &&& self.combiner@@.value.is_Ready() ==> {
            &&& self.request_ids@.len() == 0
            &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
            &&& (forall |i| #![trigger self.local_updates@[i]] 0 <= i < self.request_ids@.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.instance == inst
                &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
                //TODO: self.local_updates[i]@.value.get_Placed_idx() == self.request_ids
            })
        }

        // TODO: requires ghost_replica.state == nrifc.I(actual_replica)
        // requires ghost_replica.nodeId == node.nodeId as int
        &&& self.ghost_replica@@.key == nid
        &&& self.ghost_replica@@.instance == inst

        // TODO: requires |responses| == MAX_THREADS_PER_REPLICA as int
    }

    pub open spec fn execute_post(&self, pre: Self, nid: NodeId, responses_old: Seq<ReturnType>, responses: Seq<ReturnType>) -> bool {
        // TODO: |responses'| == MAX_THREADS_PER_REPLICA as int
        // TODO: |requestIds| <= MAX_THREADS_PER_REPLICA as int

        // XXX: a maximum number of requests so there's no overflow
        &&& self.request_ids@.len() <= MAX_REQUESTS

        // TODO: ensures combinerState.state.CombinerPlaced? ==> post_exec(node, requestIds, responses', updates', combinerState')
        &&& pre.combiner@@.value.is_Placed() ==> {
            &&& self.combiner@@.value.is_Ready()
            &&& self.combiner@@.key == pre.combiner@@.key
            &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
            &&& (forall |i| 0 <= i < self.request_ids@.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& (#[trigger] self.local_updates@[i])@.key == self.request_ids@[i as int]
                &&& self.local_updates@[i]@.instance == pre.local_updates@[i]@.instance
                &&& self.local_updates@[i]@.value.is_Done()
                &&& self.local_updates@[i]@.value.get_Done_ret() == responses[i as int]
            })
        }
        // ensures combinerState.state.CombinerReady? ==> responses == responses' && combinerState' == combinerState && updates' == updates
        &&& pre.combiner@@.value.is_Ready() ==> {
            &&& responses_old == responses
            &&& self.combiner@@ == pre.combiner@@
            &&& self.local_updates == pre.local_updates
        }
        // ensures cb' == cb
        // TODO: why does this not work?
        &&& self.cb_combiner@@ == pre.cb_combiner@@
        // requires nr.cb_loc_s == cb.cb_loc_s
        &&& self.cb_combiner@@.instance == pre.cb_combiner@@.instance
        // requires cb.nodeId == node.nodeId as int
        &&& self.cb_combiner@@.key == nid
        // requires cb.rs.CombinerIdle?
        &&& self.cb_combiner@@.value.is_Idle()

        // TODO: ensures ghost_replica'.state == nrifc.I(actual_replica')
        // ensures ghost_replica'.nodeId == node.nodeId as int
        &&& self.ghost_replica@@.key == nid
        &&& self.ghost_replica@@.instance == pre.ghost_replica@@.instance
    }
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
    pub log_entry: PCell<ConcreteLogEntry>,

    /// Indicates whether this entry represents a valid operation when on the log.
    ///
    ///  - Dafny: linear alive: Atomic<bool, CBAliveBit>)
    ///  - Rust:  pub(crate) alivef: AtomicBool,
    pub alive: AtomicBool<_, CyclicBuffer::alive_bits, _>,

    /// the index into the cyclic buffer of this entry into the cyclig buffer.
    pub cyclic_buffer_idx: Ghost<nat>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>
}

pub open spec fn wf(&self, idx: nat, cb_inst: CyclicBuffer::Instance) -> bool {
    // QUESTION: is that the right way to go??
    predicate {
        &&& self.cyclic_buffer_instance@ == cb_inst
        &&& self.cyclic_buffer_idx == idx
    }
    invariant on alive with (cyclic_buffer_idx, cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits) {
        &&& g@ === CyclicBuffer::token![ cyclic_buffer_instance@ => alive_bits => cyclic_buffer_idx@ => v ]
    }
}} // struct_with_invariants

impl BufferEntry {
    // pub open spec fn inv(&self, t: StoredType) -> bool {
    //     &&& self.log_entry.id() == t.cell_perms@.pcell
    //     &&& match t.cell_perms@.value {
    //         Some(v) => {
    //             &&& v.
    //         }
    //         None => false
    //     }
    // }

    // && t.cellContents.cell == buffer[i % LOG_SIZE as int].cell
    // && (i >= 0 ==>
    //   && t.logEntry.glSome?
    //   && t.logEntry.value.op == t.cellContents.v.op
    //   && t.logEntry.value.node_id == t.cellContents.v.node_id as int
    //   && t.logEntry.value.idx == i
    // )
}


struct_with_invariants!{
/// keeps track of the recursive state when applying updates to the unbounded log
tracked struct AppendEntriesGhostState {
    pub ghost idx : nat,
    pub ghost old_tail: nat,
    pub tracked log_entries: Map<nat, UnboundedLog::log>,
    pub tracked local_updates: Map<nat, UnboundedLog::local_updates>,
    pub tracked combiner: UnboundedLog::combiner,
    pub tracked tail: UnboundedLog::tail,
    pub ghost request_ids: Seq<ReqId>,
    pub ghost operations: Seq<UpdateOp>
}

pub open spec fn wf(&self, nid: nat, ridx: nat, inst: UnboundedLog::Instance) -> bool {
    predicate {
        // &&& self.idx == (self.request_ids.len() - ridx)
        // &&& 0 <= self.idx <= ridx
        &&& 0 <= self.idx <= self.request_ids.len()
        &&& ridx < self.request_ids.len()

        // tail value
        &&& self.tail@.value == self.old_tail + self.idx
        &&& self.tail@.instance == inst

        // combiner stuff
        &&& self.combiner@.instance == inst
        &&& self.combiner@.key == nid
        &&& self.combiner@.value.is_Placed()

        // we added all the new entries
        &&& (forall |i| 0 <= i < self.idx <==> self.log_entries.contains_key(i))
        &&& (forall |i| 0 <= i < self.request_ids.len() <==> self.local_updates.contains_key(i))

        // processed entries
        &&& (forall |i| #![trigger self.local_updates[i]] 0 <= i < self.idx ==> {
            &&& self.local_updates[i]@.instance == inst
            &&& self.local_updates[i]@.key == self.request_ids[i as int]
            &&& self.local_updates[i]@.value.is_Placed()
            &&& self.local_updates[i]@.value.get_Placed_op() == self.operations[i as int]
            // &&& self.local_updates[i]@.value.get_Placed_idx() == self.old_tail + self.idx
        })

        // unprocessed entries
        &&& (forall |i| #![trigger self.local_updates[i]] self.idx <= i < self.request_ids.len() ==> {
            &&& self.local_updates[i]@.instance == inst
            &&& self.local_updates[i]@.key == self.request_ids[i as int]
            &&& self.local_updates[i]@.value.is_Init()
            &&& self.local_updates[i]@.value.get_Init_op() == self.operations[i as int]
        })

        // the log entries
        &&& (forall |i| #![trigger self.log_entries[i]] 0 <= i < self.idx ==> {
            &&& self.log_entries[i]@.instance == inst
            &&& self.log_entries[i]@.key == self.old_tail + i
            &&& self.log_entries[i]@.value.node_id == nid
            &&& self.log_entries[i]@.value.op == self.operations[i as int]
        })
    }
}
} // struct_with_invariants!


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

        &&& self.slog.len() == self.cyclic_buffer_instance@.buffer_size()

        // && (forall i: nat | 0 <= i < LOG_SIZE as int :: buffer[i].WF(i, cb_loc_s))
        &&& (forall |i: nat| i < LOG_SIZE ==> (#[trigger] self.slog[i as int]).wf(i, self.cyclic_buffer_instance@))

        // &&& (forall |i:nat| i < LOG_SIZE ==> self.slog[i as int].inv(
        //     self.cyclic_buffer_instance@.state.contents[i].cell_perms
        // ))

        // && (forall v, g :: atomic_inv(bufferContents, v, g) <==> ContentsInv(buffer, g, cb_loc_s))

        // make sure we
        &&& self.unbounded_log_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.num_replicas() == self.num_replicas

        &&& self.cyclic_buffer_instance@.unbounded_log_instance() == self.unbounded_log_instance
    }

    // invariant on slog with (

    invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound) {
        // && (forall v, g :: atomic_inv(ctail.inner, v, g) <==> g == Ctail(v as int))
        &&& g@ === UnboundedLog::token![ unbounded_log_instance@ => version_upper_bound => v as nat ]
        &&& 0 <= v <= MAX_IDX
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head) {
        // && (forall v, g :: atomic_inv(head.inner, v, g) <==> g == CBHead(v as int, cb_loc_s))
        &&& g@ === CyclicBuffer::token![ cyclic_buffer_instance@ => head => v as nat ]
        &&& 0 <= v <= MAX_IDX
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail, CyclicBuffer::tail)) {
        // && (forall v, g :: atomic_inv(globalTail.inner, v, g) <==> GlobalTailInv(v, g, cb_loc_s))
        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance@ => tail => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance@ => tail => v as nat ]
        &&& 0 <= v <= MAX_IDX
    }


    // && (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId, cb_loc_s))
    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_versions)) {


        &&& g.0@ === UnboundedLog::token![ unbounded_log_instance@ => local_versions => i as nat => v as nat ]
        &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance@ => local_versions => i as nat => v as nat ]
        &&& 0 <= v <= MAX_IDX
    }
}
} // struct_with_invariants!{


impl NrLog
{
    /// initializes the NrLOg
    pub fn new(num_replicas: usize, log_size: usize) -> (res: Self)
        requires
            log_size == LOG_SIZE,
            num_replicas == NUM_REPLICAS
        ensures
            res.wf()
    {
        //
        // initialize the unbounded log state machine to obtain the tokens
        //
        let tracked unbounded_log_instance     : UnboundedLog::Instance;
        let tracked ul_log                     : Map<LogIdx, UnboundedLog::log>;
        let tracked ul_tail                    : UnboundedLog::tail;
        let tracked ul_replicas                : Map<NodeId,UnboundedLog::replicas>;
        let tracked mut ul_local_versions      : Map<NodeId,UnboundedLog::local_versions>;
        let tracked ul_version_upper_bound     : UnboundedLog::version_upper_bound;
        // let tracked ul_local_reads             : Map<ReqId,UnboundedLog::local_reads>;
        // let tracked ul_local_updates           : Map<ReqId,UnboundedLog::local_updates>;
        let tracked ul_combiner                : Map<NodeId,UnboundedLog::combiner>;

        proof {
            let tracked (
                Trk(unbounded_log_instance0), // Trk<Instance>,
                Trk(ul_log0), //Trk<Map<LogIdx,log>>,
                Trk(ul_tail0), //Trk<tail>,
                Trk(ul_replicas0), //Trk<Map<NodeId,replicas>>,
                Trk(ul_local_versions0), //Trk<Map<NodeId,local_versions>>,
                Trk(ul_version_upper_bound0), //Trk<version_upper_bound>,
                _, //Trk(ul_local_reads0), //Trk<Map<ReqId,local_reads>>,
                _, //Trk(ul_local_updates0), //Trk<Map<ReqId,local_updates>>,
                Trk(ul_combiner0), //Trk<Map<NodeId,combiner>>
                ) = UnboundedLog::Instance::initialize(num_replicas as nat);
            unbounded_log_instance = unbounded_log_instance0;
            ul_log = ul_log0;
            ul_tail = ul_tail0;
            ul_replicas = ul_replicas0;
            ul_local_versions = ul_local_versions0;
            ul_version_upper_bound = ul_version_upper_bound0;
            // ul_local_reads = ul_local_reads0;
            // ul_local_updates = ul_local_updates0;
            ul_combiner = ul_combiner0;
        }

        //
        // initialize the log cells
        //

        let ghost mut logical_log_idx;
        proof {
            logical_log_idx = -log_size as int;
        }

        let mut slog_entries : Vec<Option<PCell<ConcreteLogEntry>>> = Vec::with_capacity(log_size);
        let tracked mut contents: Map<LogicalLogIdx, StoredType> = Map::tracked_empty();

        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                logical_log_idx == log_idx - log_size,
                -log_size <= logical_log_idx <= 0,
                slog_entries.len() == log_idx,
                forall |i| 0 <= i < log_idx ==> (#[trigger] slog_entries[i]).is_Some(),
                forall |i| -log_size <= i < logical_log_idx <==> #[trigger] contents.contains_key(i),
                forall |i| #[trigger] contents.contains_key(i) ==> stored_type_inv(contents[i], i, unbounded_log_instance),

        {
            // pub log_entry: PCell<ConcreteLogEntry>,
            // create the log entry cell, TODO: create the concrete log entry here?
            let (pcell, token) = PCell::empty(); // empty(); // new(v)

            // add the cell to the log entries for later
            slog_entries.push(Option::Some(pcell));

            // create the stored type
            let tracked stored_type = StoredType {
                cell_perms: token.get(),
                log_entry: Option::None
            };


            // TODO: we don't put anything in there yet... convert the entry to an option
            //       and keep in sync with the alive bit?
            assert(stored_type_inv(stored_type, logical_log_idx, unbounded_log_instance));

            // add the stored type to the contents map
            contents.tracked_insert(logical_log_idx, stored_type);

            log_idx = log_idx + 1;
            proof {
                logical_log_idx = logical_log_idx + 1;
            }
        }
        assert(log_idx == log_size);
        assert(logical_log_idx == 0);


        //
        // Create the cyclic buffer state machine
        //

        let tracked cyclic_buffer_instance  : CyclicBuffer::Instance;
        let tracked cb_head                 : CyclicBuffer::head;
        let tracked cb_tail                 : CyclicBuffer::tail;
        let tracked mut cb_local_versions   : Map<NodeId, CyclicBuffer::local_versions>;
        let tracked mut cb_alive_bits       : Map<LogIdx, CyclicBuffer::alive_bits>;
        let tracked cb_combiner             : Map<NodeId, CyclicBuffer::combiner>;

        proof {
            assert(log_size == LOG_SIZE);
            assert(LOG_SIZE == spec::cyclicbuffer::LOG_SIZE);
            let tracked (
                Trk(cyclic_buffer_instance0), // CyclicBuffer::Instance>;
                Trk(cb_head0), // CyclicBuffer::head>;
                Trk(cb_tail0), // CyclicBuffer::tail>;
                Trk(cb_local_versions0), // Map<NodeId, CyclicBuffer::local_versions>;
                Trk(cb_alive_bits0), // Map<LogIdx, CyclicBuffer::alive_bits>;
                Trk(cb_combiner0), // Map<NodeId, CyclicBuffer::combiner>;
            ) = CyclicBuffer::Instance::initialize(unbounded_log_instance, log_size as nat, num_replicas as nat, contents, contents);
            cyclic_buffer_instance = cyclic_buffer_instance0;
            cb_head = cb_head0;
            cb_tail = cb_tail0;
            cb_local_versions = cb_local_versions0;
            cb_alive_bits = cb_alive_bits0;
            cb_combiner = cb_combiner0;
        }

        //
        // build up the actual log
        //

        let mut slog : Vec<BufferEntry> = Vec::with_capacity(log_size);
        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                slog_entries.len() == log_size,
                slog.len() == log_idx,
                forall |i| 0 <= i < log_idx ==> (#[trigger] slog[i]).wf(i as nat, cyclic_buffer_instance),
                forall |i| log_idx <= i < log_size ==> cb_alive_bits.contains_key(i),
                forall |i| #![trigger cb_alive_bits[i]] log_idx <= i < log_size ==> {
                    &&& cb_alive_bits[i]@.key == i
                    &&& cb_alive_bits[i]@.value == false
                    &&& cb_alive_bits[i]@.instance == cyclic_buffer_instance
                },
                forall |i| 0 <= i < log_idx ==> slog_entries.spec_index(i).is_None(),
                forall |i| log_idx <= i < log_size ==> (#[trigger] slog_entries[i]).is_Some()
        {
            let tracked cb_alive_bit;
            proof {
                cb_alive_bit = cb_alive_bits.tracked_remove(log_idx as nat);
            }

            let mut log_entry = Option::None;
            slog_entries.swap(log_idx, &mut log_entry);
            assert(log_entry.is_Some());
            let log_entry = log_entry.unwrap();

            let tracked cb_inst = tracked(cyclic_buffer_instance.clone());

            let entry = BufferEntry {
                log_entry: log_entry,
                alive: AtomicBool::new((ghost(log_idx as nat), cb_inst), false, cb_alive_bit),
                cyclic_buffer_idx: ghost(log_idx as nat),
                cyclic_buffer_instance: tracked(cyclic_buffer_instance.clone())
            };
            slog.push(entry);

            log_idx = log_idx + 1;
        }

        let tracked ul_inst = tracked(unbounded_log_instance.clone());
        let version_upper_bound = CachePadded(AtomicU64::new(ul_inst, 0, ul_version_upper_bound));

        let tracked cb_inst = tracked(cyclic_buffer_instance.clone());
        let head = CachePadded(AtomicU64::new(cb_inst, 0, cb_head));

        let tracked cb_inst = tracked(cyclic_buffer_instance.clone());
        let tracked ul_inst = tracked(unbounded_log_instance.clone());
        let tail = CachePadded(AtomicU64::new((cb_inst, ul_inst), 0, (ul_tail, cb_tail)));
        let mut local_versions : Vec<CachePadded<AtomicU64<(Tracked<UnboundedLog::Instance>, Tracked<CyclicBuffer::Instance>, int), (UnboundedLog::local_versions, CyclicBuffer::local_versions), _>>>= Vec::with_capacity(num_replicas);


        let mut nid = 0;
        while nid < num_replicas
            invariant
                0 <= nid <= num_replicas,
                local_versions.len() == nid,
                forall |i| nid <= i < num_replicas ==> ul_local_versions.contains_key(i),
                forall |i| nid <= i < num_replicas ==> cb_local_versions.contains_key(i),
                forall |i| #![trigger cb_local_versions[i]] nid <= i < num_replicas ==> {
                    &&& cb_local_versions[i]@.instance == cyclic_buffer_instance
                    &&& cb_local_versions[i]@.key == i
                    &&& cb_local_versions[i]@.value == 0
                },
                forall |i| #![trigger ul_local_versions[i]] nid <= i < num_replicas ==> {
                    &&& ul_local_versions[i]@.instance == unbounded_log_instance
                    &&& ul_local_versions[i]@.key == i
                    &&& ul_local_versions[i]@.value == 0
                },
                forall |i: int| #![trigger local_versions[i]] 0 <= i < local_versions.len() ==> {
                    // what to put here?
                    &&& local_versions[i].0.well_formed()
                    &&& local_versions[i].0.constant().0 == unbounded_log_instance
                    &&& local_versions[i].0.constant().1 == cyclic_buffer_instance
                    &&& local_versions[i].0.constant().2 == i
                }
        {
            let ghost mut nid_ghost;
            let tracked ul_version;
            let tracked cb_version;
            proof {
                nid_ghost = nid as int;
                ul_version = ul_local_versions.tracked_remove(nid as nat);
                cb_version = cb_local_versions.tracked_remove(nid as nat);
            }

            let tracked cb_inst = tracked(cyclic_buffer_instance.clone());
            let tracked ul_inst = tracked(unbounded_log_instance.clone());

            local_versions.push(CachePadded(AtomicU64::new((ul_inst, cb_inst, nid_ghost), 0, (ul_version, cb_version))));

            nid = nid + 1;
        }

        NrLog {
            slog,
            version_upper_bound,
            head,
            tail,
            local_versions,
            num_replicas : ghost(num_replicas as nat),
            unbounded_log_instance: tracked(unbounded_log_instance),
            cyclic_buffer_instance: tracked(cyclic_buffer_instance),
        }
    }


    /// Returns a physical index given a logical index into the shared log.
    #[inline(always)]
    pub(crate) fn index(&self, logical: u64) -> (result: usize)
        requires
            self.slog.len() == LOG_SIZE
        ensures
            result as nat == self.index_spec(logical as nat),
            result == spec::cyclicbuffer::log_entry_idx(logical as int, self.slog.spec_len() as nat),
            result < self.slog.len()
    {
        (logical as usize) % self.slog.len()
    }

    pub (crate) open spec fn index_spec(&self, logical: nat) -> nat
        recommends self.slog.len() == LOG_SIZE
    {
        logical % (self.slog.len() as nat)
    }

    #[inline(always)]
    pub(crate) fn is_alive_value(&self, logical: u64) -> (result: bool)
        requires
            self.slog.len() == LOG_SIZE
        ensures
            result == self.is_alive_value_spec(logical as int),
            result == spec::cyclicbuffer::log_entry_alive_value(logical as int, self.slog.spec_len() as nat)
    {
        ((logical as usize) / LOG_SIZE % 2) == 0
    }

    pub(crate) open spec fn is_alive_value_spec(&self, logical: int) -> bool
        recommends self.slog.len() == LOG_SIZE
    {
        ((logical / (LOG_SIZE as int)) % 2) == 0
    }


    /// This method returns the current version upper bound value for the log.
    ///
    ///  - Rust: get_ctail()
    ///  - Dafny: n/a part of do-read
    pub(crate) fn get_version_upper_bound(&self, local_reads: Tracked<UnboundedLog::local_reads>)
        -> (ret: (u64, Tracked<UnboundedLog::local_reads>))
        requires
            self.wf(),
            local_reads@@.instance == self.unbounded_log_instance@,
            local_reads@@.value.is_Init()
        ensures
            ret.1@@.value.is_VersionUpperBound(),
            ret.1@@.value.get_VersionUpperBound_version_upper_bound() == ret.0 as nat,
            ret.1@@.value.get_VersionUpperBound_op() == local_reads@@.value.get_Init_op(),
            ret.1@@.instance == self.unbounded_log_instance@,
            ret.1@@.key == local_reads@@.key
    {
        let tracked local_reads = local_reads.get();
        let ghost rid = local_reads@.key;

        let tracked new_local_reads_g : UnboundedLog::local_reads;

        let res = atomic_with_ghost!(
            &self.version_upper_bound.0 => load();
            returning res;
            ghost g => {
                new_local_reads_g = self.unbounded_log_instance.borrow().readonly_version_upper_bound(rid, &g, local_reads);
            }
        );

        (res, tracked(new_local_reads_g))
    }

    /// checks whether the version of the local replica has advanced enough to perform read operations
    ///
    /// This basically corresponds to the transition `readonly_read_to_read` in the unbounded log.
    ///
    // https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/log.rs#L525
    pub fn is_replica_synced_for_reads(&self, node_id: ReplicaId, version_upper_bound: u64,
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
            result.0 ==> result.1@@.value.get_ReadyToRead_node_id() == node_id,
            result.0 ==> result.1@@.value.get_ReadyToRead_op() == local_reads@@.value.get_VersionUpperBound_op(),
            !result.0 ==> result.1 == local_reads,
            result.1@@.instance == self.unbounded_log_instance@,
            result.1@@.key == local_reads@@.key
    {
        // obtain the request id from the local_reads token
        let rid_g : Ghost<ReqId> = ghost(local_reads@@.key);
        let tracked new_local_reads_g: UnboundedLog::local_reads;

        // obtain the local version
        let local_version = &self.local_versions.index(node_id as usize).0;

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


    proof fn unbounded_log_append_entries(tracked &self, nid: nat, ridx: nat, tracked state: AppendEntriesGhostState) -> (tracked ret: AppendEntriesGhostState)
        requires
            self.wf(),
            state.idx == 0,
            state.wf(nid, ridx, self.unbounded_log_instance@),
        ensures
            ret.request_ids == state.request_ids,
            ret.operations == state.operations,
            ret.idx == ridx + 1,
            ret.old_tail == state.old_tail,
            ret.wf(nid, ridx, self.unbounded_log_instance@),
        decreases
            ridx
    {
        let tracked mut state = state;      // make it tracked

        if ridx != 0 {
            state = self.unbounded_log_append_entries(nid, (ridx - 1) as nat, state);
            assert(state.idx == ridx);
            // assume we've iterated up to idx - 1
        } else {
            assert(state.idx == 0);
        }

        let tracked AppendEntriesGhostState {
            idx,
            old_tail,
            mut log_entries,
            mut local_updates,
            combiner,
            mut tail,
            request_ids,
            operations
        } = state;

        // get the local update and the
        let reqid = request_ids[ridx as int];
        let tracked local_update = local_updates.tracked_remove(ridx);

        let tracked update_result = self.unbounded_log_instance.borrow()
            .update_place_ops_in_log_one(nid as nat, reqid, &mut tail, local_update, combiner);
        // that one here should be fine I suppose...
        // assert(local_update@.value.get_Placed_idx() == tail@.value - 1);

        let tracked combiner = update_result.2.0;
        log_entries.tracked_insert(ridx, update_result.0.0);
        local_updates.tracked_insert(ridx, update_result.1.0);

        let tracked res = AppendEntriesGhostState {
            idx : idx + 1,
            old_tail,
            log_entries,
            local_updates,
            combiner,
            tail,
            request_ids,
            operations
        };
        res
    }


    /// Inserts a slice of operations into the log.
    pub fn append(&self, replica_token: &ReplicaToken, operations: &Vec<UpdateOp>,
        responses: &Vec<ReturnType>,
        ghost_data_in: Tracked<NrLogAppendExecDataGhost>
    ) -> (result: Tracked<NrLogAppendExecDataGhost>)
        requires
            self.wf(),
            replica_token@ < self.local_versions.len(),
            ghost_data_in@.append_pre(operations@, replica_token@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
            operations.len() <= MAX_REQUESTS
        ensures
            result@.append_post(replica_token@,  self.unbounded_log_instance@, self.cyclic_buffer_instance@, operations@, responses@)
    {
        let nid = replica_token.id() as usize;

        // // TODO!
        let nops = operations.len();

        // somehow can't really do this as a destructor
        let tracked mut ghost_data = ghost_data_in.get();

        let mut iteration = 1;
        let mut waitgc = 1;

        loop
            invariant
                self.wf(),
                0 <= waitgc <= WARN_THRESHOLD,
                0 <= iteration <= WARN_THRESHOLD,
                replica_token@ < self.local_versions.len(),
                nid == replica_token@,
                nops == operations.len(),
                nops <= MAX_REQUESTS,
                ghost_data.append_pre(operations@, replica_token@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
        {
            // unpack stuff
            let tracked mut local_updates = ghost_data.local_updates.get();// Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
            let tracked ghost_replica = ghost_data.ghost_replica;      // Tracked<UnboundedLog::replicas>,
            let tracked mut combiner = ghost_data.combiner.get();          // Tracked<UnboundedLog::combiner>,
            let tracked mut cb_combiner = ghost_data.cb_combiner.get();    // Tracked<CyclicBuffer::combiner>,
            let tracked request_ids = ghost_data.request_ids;          // Ghost<Seq<ReqId>>,

            if iteration == WARN_THRESHOLD {
                print_starvation_warning(line!());
                iteration = 0;
                // TODO: return;
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
                    assert(g.view().instance == self.cyclic_buffer_instance.view());
                    assert(cb_combiner.view().instance == self.cyclic_buffer_instance.view());
                    assert(cb_combiner.view().key == nid);
                    assert(cb_combiner.view().value.is_Idle());
                    cb_combiner = self.cyclic_buffer_instance
                        .borrow()
                        .advance_tail_start(nid as nat, &g, cb_combiner);
                }
            );

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

                waitgc = waitgc + 1;

                proof {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_tail_abort(nid as nat, cb_combiner);
                }


                // TODO: call execute here!
                // // assemble the struct again
                // ghost_data = NrLogAppendExecDataGhost {
                //     local_updates: tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                //     ghost_replica,  // Tracked<UnboundedLog::replicas>,
                //     combiner: tracked(combiner),       // Tracked<UnboundedLog::combiner>,
                //     cb_combiner: tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
                //     request_ids,    // Ghost<Seq<ReqId>>,
                // };

                // // let tracked execute_res = self.execute(replica_token, responses, tracked(ghost_data));

                // ghost_data = execute_res.get();
                // local_updates = ghost_data.local_updates.get(); // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                // ghost_replica = ghost_data.ghost_replica;       // Tracked<UnboundedLog::replicas>,
                // combiner = ghost_data.combiner.get();           // Tracked<UnboundedLog::combiner>,
                // cb_combiner = ghost_data.cb_combiner.get();     // Tracked<CyclicBuffer::combiner>,
                // request_ids = ghost_data.request_ids;           // Ghost<Seq<ReqId>>,

                let advance_head_res = self.advance_head(replica_token, tracked(cb_combiner));
                cb_combiner = advance_head_res.get();

                // assemble the struct again
                ghost_data = NrLogAppendExecDataGhost {
                    local_updates: tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                    ghost_replica,  // Tracked<UnboundedLog::replicas>,
                    combiner: tracked(combiner),       // Tracked<UnboundedLog::combiner>,
                    cb_combiner: tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
                    request_ids,    // Ghost<Seq<ReqId>>,
                };

                continue;
            }

            assert(nops <= MAX_REQUESTS);
            assert(tail <= MAX_IDX);

            let new_tail = tail + (nops as u64);

            // capture the warning here
            if new_tail >= MAX_IDX {
                panic_with_tail_too_big();
                ////////////////////////////////////////////////////////////////////////////////////
                // !!! THIS IS A PANIC CASE! WE DO NOT RETURN FROM HERE !!!
                // !!! JUST MAKING THE POST CONDITION PASS !!!
                ////////////////////////////////////////////////////////////////////////////////////
                proof {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_tail_abort(nid as nat, cb_combiner);
                }

                ghost_data = NrLogAppendExecDataGhost {
                    local_updates:tracked(Map::tracked_empty()),   // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                    ghost_replica,                              // Tracked<UnboundedLog::replicas>,
                    combiner: tracked(combiner),                // Tracked<UnboundedLog::combiner>,
                    cb_combiner: tracked(cb_combiner),          // Tracked<CyclicBuffer::combiner>,
                    request_ids: ghost(Seq::empty()),              // Ghost<Seq<ReqId>>,
                };

                return tracked(ghost_data);
            }

            // If on adding in the above entries there would be fewer than `GC_FROM_HEAD`
            // entries left on the log, then we need to advance the head of the log.
            let advance = new_tail > head + (self.slog.len() - GC_FROM_HEAD) as u64 ;

            // Try reserving slots for the operations. If that fails, then restart
            // from the beginning of this loop.
            // if self.tail.compare_exchange_weak(tail, tail + nops, Ordering::Acquire, Ordering::Acquire) !+ Ok(tail) {
            //     continue;
            // }

            let tracked advance_tail_finish_result : (Gho<Map<LogicalLogIdx,StoredType>>, Trk<Map<LogicalLogIdx, StoredType>>, Trk<CyclicBuffer::combiner>);
            let tracked mut append_entries_ghost_state : AppendEntriesGhostState;
            let tracked mut cb_log_entries : Map<int, StoredType> = Map::tracked_empty();
            let tracked mut log_entries : Map<nat,UnboundedLog::log> = Map::tracked_empty();

            // seems required to get the contains properly
            assert(forall |i| 0 <= i < request_ids@.len() ==> local_updates.contains_key(i));

            // let tracked local_update ;// UnboundedLog::local_updates
            let result = atomic_with_ghost!(
                &self.tail.0 => compare_exchange(tail, new_tail);
                update prev -> next;
                returning result;
                ghost g => {
                    if matches!(result, Result::Ok(tail)) {
                        let tracked (mut unbounded_tail, mut cb_tail) = g;

                        assert(tail <= new_tail);
                        assert(new_tail <= head + self.slog.len());

                        advance_tail_finish_result = self.cyclic_buffer_instance.borrow()
                            .advance_tail_finish(nid as nat, new_tail as nat, &mut cb_tail, cb_combiner);

                        cb_combiner = advance_tail_finish_result.2.0;
                        cb_log_entries = advance_tail_finish_result.1.0;

                        // TODO: how to do this lool?
                        // TODO: is this the right way to go about this? This is where we differ,
                        // we now do just a single insert
                        if request_ids.view().len() > 0 {

                            // transition to the placed phase
                            combiner = self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);

                            // TODO: proof vs. spec mode!
                            append_entries_ghost_state = AppendEntriesGhostState {
                                idx : 0,
                                old_tail: tail as nat,
                                log_entries,
                                local_updates,
                                combiner,
                                tail: unbounded_tail,
                                request_ids: request_ids.view(),
                                operations: operations.view()
                            };

                            append_entries_ghost_state = self.unbounded_log_append_entries(nid as nat, (request_ids.view().len() - 1) as nat, append_entries_ghost_state);
                            log_entries = append_entries_ghost_state.log_entries;
                            combiner = append_entries_ghost_state.combiner;
                            unbounded_tail = append_entries_ghost_state.tail;
                            local_updates = append_entries_ghost_state.local_updates;
                        }

                        g = (unbounded_tail, cb_tail);

                        // need to get the loop done above!
                        assert(g.0.view().value == next);
                        // need some bounds to avoid overflow!
                        assert(next < MAX_IDX);

                    } else {
                        cb_combiner = self.cyclic_buffer_instance
                            .borrow()
                            .advance_tail_abort(nid as nat, cb_combiner);
                    }
                }
            );

            if !matches!(result, Result::Ok(tail)) {
                // assemble the struct again
                ghost_data = NrLogAppendExecDataGhost {
                    local_updates: tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                    ghost_replica,  // Tracked<UnboundedLog::replicas>,
                    combiner: tracked(combiner),       // Tracked<UnboundedLog::combiner>,
                    cb_combiner: tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
                    request_ids,    // Ghost<Seq<ReqId>>,
                };
                continue;
            }


            assert(self.cyclic_buffer_instance@.buffer_size() == LOG_SIZE);
            assert(forall |i| tail - LOG_SIZE <= i < new_tail - LOG_SIZE <==> cb_log_entries.contains_key(i));
            assert(forall |i| cb_log_entries.contains_key(i) ==> {
                &&& stored_type_inv(#[trigger] cb_log_entries.index(i), i, self.unbounded_log_instance@)
            });

            assert(forall |i| 0 <= i < request_ids@.len() ==> #[trigger]log_entries.contains_key(i));

            assert(forall |i| #![trigger log_entries[i]] 0 <= i < request_ids@.len() ==> {
                &&& log_entries[i]@.instance == self.unbounded_log_instance@
             });
             assert(forall |i| #![trigger log_entries[i]] 0 <= i < request_ids@.len() ==> {
                &&& log_entries[i]@.key == tail + i
             });

            assert(forall |i| #![trigger log_entries[i]] 0 <= i < request_ids@.len() ==> {
                &&& #[trigger]log_entries.contains_key(i)
                &&& log_entries[i]@.key == tail + i
                &&& log_entries[i]@.instance == self.unbounded_log_instance@
             });




            // Successfully reserved entries on the shared log. Add the operations in.
            let mut idx = 0;
            while idx < nops
                invariant
                    self.wf(),
                    0 <= idx <= nops,
                    tail + idx <= new_tail,
                    tail + nops == new_tail,
                    nops == operations.len(),
                    nops == request_ids@.len(),
                    cb_combiner@.key == nid,
                    cb_combiner@.value.is_Appending(),
                    cb_combiner@.value.get_Appending_cur_idx() == tail + idx,
                    cb_combiner@.value.get_Appending_tail() == new_tail,
                    cb_combiner@.value.get_Appending_cur_idx() <= cb_combiner@.value.get_Appending_tail(),
                    cb_combiner@.instance == self.cyclic_buffer_instance@,
                    forall |i| #![trigger log_entries[i]] idx <= i < request_ids@.len() ==> {
                       &&& #[trigger]log_entries.contains_key(i)
                       &&& log_entries[i]@.key == tail + i
                       &&& log_entries[i]@.instance == self.unbounded_log_instance@
                       &&& log_entries[i]@.value.node_id == nid as nat
                       &&& log_entries[i]@.value.op == operations[i as int]
                       // && log_entries[i] == Log(tail as int + i, ops[i], node.nodeId as int)
                    },
                    forall |i| #![trigger local_updates[i]] 0 <= i < request_ids@.len() ==> {
                        &&& local_updates.contains_key(i)
                        &&& local_updates[i]@.value.is_Placed()
                        &&& local_updates[i]@.value.get_Placed_op() == operations[i as int]
                    },
                    forall |i| (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE <==> cb_log_entries.contains_key(i),
                    forall |i| cb_log_entries.contains_key(i) ==> stored_type_inv(#[trigger] cb_log_entries.index(i), i, self.unbounded_log_instance@),
                    // forall|i: int| idx <= i < nops ==> (#[trigger] cb_log_entries[i]).cell_perms@.pcell == self.slog.spec_index(
                    //     self.index_spec((tail + i) as nat) as int).log_entry.id(),
            {
                let tracked cb_log_entry;
                proof {
                    cb_log_entry = cb_log_entries.tracked_remove((tail + idx) - LOG_SIZE);
                }
                let mut cb_log_entry_perms = tracked(cb_log_entry.cell_perms);

                assert(cb_combiner@.value.get_Appending_cur_idx() < cb_combiner@.value.get_Appending_tail());

                //let tracked log_entry = log_entry.tracked_remove(idx);

                // the logical index into the log
                let logical_log_idx = tail + idx as u64;
                let log_idx = self.index(logical_log_idx);

                // unsafe { (*e).operation = Some(op.clone()) };
                // unsafe { (*e).replica = idx.0 };
                let new_log_entry = ConcreteLogEntry {
                    op: operations.index(idx as usize).clone(),
                    node_id: nid as u64,
                };

                // TODO: need to link the permission with the log entry cell
                assert(cb_log_entry_perms@@.pcell == self.slog.spec_index(log_idx as int).log_entry.id());

                // update the log entry in the buffer
                self.slog.index(log_idx).log_entry.replace(&mut cb_log_entry_perms, new_log_entry);

                assert(cb_log_entry_perms@@.value.is_Some());
                assert(cb_log_entry_perms@@.value.get_Some_0().node_id == nid as u64);
                assert(cb_log_entry_perms@@.value.get_Some_0().op == operations.spec_index(idx as int));

                // unsafe { (*e).alivef.store(m, Ordering::Release) };
                let m = self.is_alive_value(logical_log_idx as u64);

                let tracked append_flip_bit_result;
                let tracked new_stored_type;

                atomic_with_ghost!(
                    &self.slog.index(log_idx).alive => store(m);
                    ghost g => {
                        new_stored_type = StoredType {
                            cell_perms: cb_log_entry_perms.get(),
                            log_entry: Option::Some(log_entries.tracked_remove(idx as nat)),
                        };

                        let c_cur_idx = cb_combiner.view().value.get_Appending_cur_idx();

                        assert(stored_type_inv(new_stored_type, c_cur_idx as int, self.unbounded_log_instance.view()));

                        append_flip_bit_result = self.cyclic_buffer_instance.borrow()
                            .append_flip_bit(nid as NodeId, new_stored_type, new_stored_type, g, cb_combiner);
                        g = append_flip_bit_result.0.0;
                        cb_combiner = append_flip_bit_result.1.0;
                    }
                );

                idx = idx + 1;
            }

            proof {
                cb_combiner = self.cyclic_buffer_instance.borrow().append_finish(nid as nat, cb_combiner);
            }

            if advance {
                let advance_head_res = self.advance_head(replica_token, tracked(cb_combiner));
                cb_combiner = advance_head_res.get();
            }

            ghost_data = NrLogAppendExecDataGhost {
                local_updates:tracked(local_updates),   // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                ghost_replica,                          // Tracked<UnboundedLog::replicas>,
                combiner: tracked(combiner),            // Tracked<UnboundedLog::combiner>,
                cb_combiner: tracked(cb_combiner),      // Tracked<CyclicBuffer::combiner>,
                request_ids,                            // Ghost<Seq<ReqId>>,
            };

            return tracked(ghost_data);
        }

    }


    /// Advances the head of the log forward. If a replica has stopped making
    /// progress, then this method will never return. Accepts a closure that is
    /// passed into execute() to ensure that this replica does not deadlock GC.
    pub fn advance_head(&self, replica_token: &ReplicaToken,
        cb_combiner: Tracked<CyclicBuffer::combiner>)
         -> (result: Tracked<CyclicBuffer::combiner>)
        requires
            self.wf(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle()
        ensures
            result@@.instance == self.cyclic_buffer_instance@,
            result@@.key == cb_combiner@@.key,
            result@@.value.is_Idle()
    {
        let tracked mut g_cb_comb_new = cb_combiner.get();
        let ghost g_node_id = cb_combiner@@.key;

        let mut iteration = 1;
        loop
            invariant
                self.wf(),
                g_cb_comb_new@.instance == self.cyclic_buffer_instance@,
                g_cb_comb_new@.value.is_Idle(),
                g_cb_comb_new@.key == g_node_id,
                g_node_id == cb_combiner@@.key,
                0 <= iteration <= WARN_THRESHOLD
        {
            // TODO
            // let global_head = self.head.load(Ordering::Relaxed);
            let global_head = atomic_with_ghost!(
                &self.head.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );

            // let f = self.tail.load(Ordering::Relaxed);
            let global_tail = atomic_with_ghost!(
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
    }

    // proof fn foo<A>(a: Seq<A>, b: Seq<A>)
    //     requires a.len() == 0 && b.len() == 0
    //     ensures a == b
    // {
    //     assert(a == Seq::empty());
    //     assert(b == Seq::empty());
    // }


    /// Executes a passed in closure (`d`) on all operations starting from a
    /// replica's local tail on the shared log. The replica is identified
    /// through an `idx` passed in as an argument.
    pub(crate) fn execute(&self, replica_token: &ReplicaToken,
        responses: &mut Vec<ReturnType>,
        actual_replica: &mut DataStructureType,
        ghost_data: Tracked<NrLogAppendExecDataGhost>
    ) -> (result: Tracked<NrLogAppendExecDataGhost>)
        requires
            self.wf(),
            old(responses).len() == 0,
            replica_token@ < self.local_versions.len(),
            ghost_data@.execute_pre(replica_token@, self.unbounded_log_instance@, self.cyclic_buffer_instance@)
        ensures
            result@.execute_post(ghost_data@, replica_token@, old(responses)@, responses@)

    {
        let nid = replica_token.id() as usize;

        // somehow can't really do this as a destructor
        let tracked ghost_data = ghost_data.get();
        let tracked mut local_updates = ghost_data.local_updates.get(); // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
        let tracked mut ghost_replica = ghost_data.ghost_replica.get(); // Tracked<UnboundedLog::replicas>,
        let tracked mut combiner = ghost_data.combiner.get();           // Tracked<UnboundedLog::combiner>,
        let tracked mut cb_combiner = ghost_data.cb_combiner.get();     // Tracked<CyclicBuffer::combiner>,
        let ghost mut request_ids = ghost_data.request_ids@;            // Ghost<Seq<ReqId>>,

        // if the combiner ins idle, we start it with the trival start transition
        proof {
            if combiner@.value.is_Ready() {
                assert(combiner@.value.is_Ready());
                assert(combiner@.key == nid);
                assert(combiner@.instance == self.unbounded_log_instance@);
                combiner = self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);
                request_ids = Seq::empty();
            }
        }

        // let ltail = self.ltails[idx.0 - 1].load(Ordering::Relaxed);
        let mut local_version = atomic_with_ghost!(
            &self.local_versions.index(nid).0 => load();
            returning ret;
            ghost g => {
                // this kicks of the state transition in both the cyclic buffer and the unbounded log
                combiner = self.unbounded_log_instance.borrow().exec_load_local_version(nid as nat, &g.0, combiner);
                cb_combiner = self.cyclic_buffer_instance.borrow().reader_start(nid as nat, &g.1, cb_combiner);
            }
        );

        // Check if we have any work to do by comparing our local tail with the log's
        // global tail. If they're equal, then we're done here and can simply return.
        // let gtail = self.tail.load(Ordering::Relaxed);
        let global_tail = atomic_with_ghost!(
            &self.tail.0 => load();
            returning global_tail;
            ghost g => {
                if (local_version == global_tail) {
                    // there has ben no additional updates to be applied, combiner back to idle
                    combiner = self.unbounded_log_instance.borrow().exec_finish_no_change(nid as nat, &g.0, combiner);
                    cb_combiner = self.cyclic_buffer_instance.borrow().reader_abort(nid as nat, cb_combiner);
                } else {
                    combiner = self.unbounded_log_instance.borrow().exec_load_global_head(nid as nat, &g.0, combiner);
                    cb_combiner = self.cyclic_buffer_instance.borrow().reader_enter(nid as nat,  &g.1, cb_combiner);
                }
            }
        );

        if local_version == global_tail {
            let tracked combiner = tracked(combiner);
            let tracked cb_combiner = tracked(cb_combiner);
            let tracked ghost_replica = tracked(ghost_replica);
            let tracked local_updates = tracked(local_updates);
            let tracked request_ids = ghost(request_ids);
            let tracked ghost_data = NrLogAppendExecDataGhost {
                local_updates,  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                ghost_replica,  // Tracked<UnboundedLog::replicas>,
                combiner,       // Tracked<UnboundedLog::combiner>,
                cb_combiner,    // Tracked<CyclicBuffer::combiner>,
                request_ids,    // Ghost<Seq<ReqId>>,
            };
            let res = tracked(ghost_data);
            assert(res@.execute_post(ghost_data, replica_token@, responses@, responses@));
            return res;
        }


        let mut responses_idx : usize = 0;

        assert(local_version <= global_tail);


        // Execute all operations from the passed in offset to the shared log's tail.
        // Check if the entry is live first; we could have a replica that has reserved
        // entries, but not filled them into the log yet.
        // for i in ltail..gtail {
        while local_version < global_tail
            invariant
                self.wf(),
                0 <= local_version <= global_tail,
                0 <= responses_idx as nat <= request_ids.len(),
                responses.len() == responses_idx,
                request_ids.len() <= MAX_REQUESTS,
                ghost_replica@.instance == self.unbounded_log_instance@,
                ghost_replica@.key == nid as nat,
                cb_combiner@.key == nid as nat,
                cb_combiner@.instance == self.cyclic_buffer_instance@,
                cb_combiner@.value.is_Reading(),
                cb_combiner@.value.get_Reading_0().is_Range(),
                cb_combiner@.value.get_Reading_0().get_Range_cur() == local_version,
                cb_combiner@.value.get_Reading_0().get_Range_end() == global_tail,
                combiner@.key == nid as nat,
                combiner@.instance == self.unbounded_log_instance@,
                combiner@.value.is_Loop(),
                combiner@.value.get_Loop_queued_ops() == request_ids,
                combiner@.value.get_Loop_lversion() == local_version,
                combiner@.value.get_Loop_tail() == global_tail,
                combiner@.value.get_Loop_idx() == responses_idx,
                forall |i| 0 <= i < request_ids.len() <==>  #[trigger]local_updates.contains_key(i),
                forall |i| #![trigger local_updates[i]] responses_idx <= i < request_ids.len() ==>  {
                    &&& local_updates.contains_key(i)
                    &&& local_updates[i]@.value.is_Placed()
                    &&& local_updates[i]@.key == request_ids[i as int]
                    &&& local_updates[i]@.instance == self.unbounded_log_instance@
                },
                forall |i| #![trigger local_updates[i]]  0 <= i < responses_idx ==> {
                    &&& local_updates.contains_key(i)
                    &&& local_updates[i]@.key == request_ids[i as int]
                    &&& local_updates[i]@.value.is_Applied()
                    &&& local_updates[i]@.value.get_Applied_ret() == responses[i as int]
                    &&& local_updates[i]@.instance == self.unbounded_log_instance@
                },
                forall |i| #[trigger] local_updates.contains_key(i) ==> {
                    &&& local_updates[i]@.instance == self.unbounded_log_instance@
                }
        {
            // calculating the actual index and the
            let phys_log_idx = self.index(local_version);
            let is_alive_value = self.is_alive_value(local_version);

            let mut iteration = 1;
            let mut is_alive = false;
            // while unsafe { (*e).alivef.load(Ordering::Acquire) != self.lmasks[idx.0 - 1].get() } {
            while !is_alive
                invariant
                    self.wf(),
                    local_version < global_tail,
                    phys_log_idx < self.slog.len(),
                    phys_log_idx as nat == self.index_spec(local_version as nat),
                    is_alive_value == self.is_alive_value_spec(local_version as int),
                    0 <= iteration <= WARN_THRESHOLD,
                    cb_combiner@.instance == self.cyclic_buffer_instance@,
                    cb_combiner@.key == nid as nat,
                    cb_combiner@.value.is_Reading(),
                    !is_alive ==> cb_combiner@.value.get_Reading_0().is_Range(),
                    !is_alive ==> cb_combiner@.value.get_Reading_0().get_Range_cur() == local_version,
                    !is_alive ==> cb_combiner@.value.get_Reading_0().get_Range_end() == global_tail,
                    is_alive ==> cb_combiner@.value.get_Reading_0().is_Guard(),
                    is_alive ==> cb_combiner@.value.get_Reading_0().get_Guard_cur() == local_version,
                    is_alive ==> cb_combiner@.value.get_Reading_0().get_Guard_end() == global_tail,
                    self.slog.spec_index(phys_log_idx as int).wf(phys_log_idx as nat, self.cyclic_buffer_instance@)
            {
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    iteration = 0;
                }

                let tracked reader_guard_result : (Gho<Map<int, StoredType>>,Trk<CyclicBuffer::combiner>);
                let alive_bit = atomic_with_ghost!(
                    &self.slog.index(phys_log_idx).alive => load();
                    returning alive_bit;
                    ghost g => {
                        if alive_bit == is_alive_value {
                            assert(g.view().key == phys_log_idx);
                            reader_guard_result = self.cyclic_buffer_instance.borrow().reader_guard(nid as nat, &g, cb_combiner);
                            cb_combiner = reader_guard_result.1.0;
                        }
                    });

                is_alive = alive_bit == is_alive_value;
                iteration = iteration + 1;
            }

            // dispatch the operation to apply the update to the replica
            // unsafe { d((*e).operation.as_ref().unwrap().clone(),(*e).replica == idx.0,) };

            let tracked stored_entry : &StoredType;
            proof {
                stored_entry = self.cyclic_buffer_instance.borrow().guard_guards(nid as nat, &cb_combiner);
            }

            assert(stored_entry == cb_combiner@.value.get_Reading_0().get_Guard_val());

            // read the entry
            // TODO: how can we tie the token obtained from the state machine to the log entry?
            assert(self.slog.spec_index(phys_log_idx as int).log_entry.id() == stored_entry.cell_perms@.pcell);
            assert(stored_entry.cell_perms@.value.is_Some());
            let log_entry = self.slog.index(phys_log_idx).log_entry.borrow(tracked_exec_borrow(&stored_entry.cell_perms));

            // actual_replica', ret := nrifc.do_update(actual_replica', log_entry.op);

            let res = actual_replica.update(log_entry.op.clone());

            assert(stored_entry.log_entry.get_Some_0()@.instance == self.unbounded_log_instance);
            assert(stored_entry.log_entry.get_Some_0()@.key == combiner.view().value.get_Loop_lversion());

            if log_entry.node_id == nid as u64 {

                // assert(local_updates.contains_key(responses_idx as nat));

                // local dispatch
                proof {
                    // unwrap the entry
                    if let Option::Some(e) = &stored_entry.log_entry {
                        assert(e.view().value.node_id == nid);

                        assert(responses_idx < request_ids.len());
                        let tracked local_update = local_updates.tracked_remove(responses_idx as nat);
                        let rid = request_ids[responses_idx as int];

                        self.unbounded_log_instance.borrow().pre_exec_dispatch_local(
                            nid as nat,
                            e,
                            &combiner
                        );

                        // let rid = combiner.view().value.get_Loop_queued_ops()[responses_idx as int];
                        assert(local_update@.value.is_Placed());
                        let tracked exec_dispatch_local_result = self.unbounded_log_instance.borrow()
                            .exec_dispatch_local(nid as nat, e, ghost_replica, local_update, combiner);
                        ghost_replica = exec_dispatch_local_result.0.0;

                        assert(exec_dispatch_local_result.1.0@.value.is_Applied());
                        assert(exec_dispatch_local_result.1.0@.value.get_Applied_ret() == res);

                        local_updates.tracked_insert(responses_idx as nat, exec_dispatch_local_result.1.0);
                        combiner = exec_dispatch_local_result.2.0;


                    } else {
                        assert(false);
                    }
                }

                responses.push(res);

                responses_idx = responses_idx + 1;

                assert(combiner@.value.get_Loop_idx() == responses_idx);

            } else {
                // remote dispatch
                proof {
                    assert(stored_entry.log_entry.get_Some_0().view().value.node_id != nid);
                    if let Option::Some(e) = &stored_entry.log_entry {
                        assert(e.view().value.node_id != nid);
                        // assert(ghost_replica@.key == nid as nat);
                        // assert(combiner@.value.get_Loop_lversion() < combiner@.value.get_Loop_tail());
                        let tracked exec_dispatch_remote_result =
                            self.unbounded_log_instance.borrow().exec_dispatch_remote(nid as nat, e, ghost_replica, combiner);
                        ghost_replica = exec_dispatch_remote_result.0.0;
                        combiner = exec_dispatch_remote_result.1.0;
                    } else {
                        assert(false)
                    }



                }
                assert(combiner@.value.get_Loop_idx() == responses_idx);
            }

            proof {
                cb_combiner = self.cyclic_buffer_instance.borrow().reader_unguard(nid as nat, cb_combiner);
            }

            local_version = local_version + 1;
        }


        assert(cb_combiner@.value.is_Reading());
        assert(cb_combiner@.value.get_Reading_0().is_Range());
        assert(cb_combiner@.value.get_Reading_0().get_Range_cur() == cb_combiner@.value.get_Reading_0().get_Range_end());

        // Update the completed tail after we've executed these operations. Also update
        // this replica's local tail.
        // Finds the maximum of the current value and the argument val, and sets the new value to the result.
        // Returns the previous value.
        // self.ctail.fetch_max(gtail, Ordering::Relaxed);

        atomic_with_ghost!(
            &self.version_upper_bound.0 => fetch_max(global_tail);
            ghost g => {
                combiner = self.unbounded_log_instance.borrow().exec_update_version_upper_bound(nid as nat, &mut g, combiner);
                // TODO: perform_UpdateDoneMultiple()
                // local_updates = local_updates;
            });


        // assert(global_tail < MAX_IDX);


        let tracked reader_finish_result : (Trk<CyclicBuffer::local_versions>, Trk<CyclicBuffer::combiner>);
        let tracked exec_finish_result : (Trk<UnboundedLog::local_versions>,Trk<UnboundedLog::combiner>);
        // self.ltails[idx.0 - 1].store(gtail, Ordering::Relaxed);
        atomic_with_ghost!(
            &self.local_versions.index(nid).0 => store(global_tail);
            ghost g => {
                exec_finish_result = self.unbounded_log_instance.borrow().exec_finish(nid as nat, g.0, combiner);
                reader_finish_result = self.cyclic_buffer_instance.borrow().reader_finish(nid as nat, g.1, cb_combiner);

                combiner = exec_finish_result.1.0;
                cb_combiner = reader_finish_result.1.0;

                g = (exec_finish_result.0.0, reader_finish_result.0.0);
        });

        let tracked combiner = tracked(combiner);
        let tracked cb_combiner = tracked(cb_combiner);
        let tracked local_updates = tracked(local_updates);
        let tracked ghost_replica = tracked(ghost_replica);
        let tracked request_ids = ghost(request_ids);
        let tracked ghost_data = NrLogAppendExecDataGhost {
            local_updates,  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
            ghost_replica,  // Tracked<UnboundedLog::replicas>,
            combiner,       // Tracked<UnboundedLog::combiner>,
            cb_combiner,    // Tracked<CyclicBuffer::combiner>,
            request_ids,    // Ghost<Seq<ReqId>>,
        };
        assume(false);
        tracked(ghost_data)
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
            result.0 <= MAX_IDX,
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
                min_local_version <= MAX_IDX,
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

/// Data for a pending operation.
///
///  - Dafny: datatype OpResponse
///  - Rust:  pub struct PendingOperation<T, R, M> {
///
/// In Dafny those data types are not options, but in Rust they are
pub struct PendingOperation {
    /// the operation that is being executed
    pub(crate) op: UpdateOp,
    /// the response of the operation
    pub(crate) resp: Option<ReturnType>,
}

impl PendingOperation {
    pub fn new(op: UpdateOp) -> (res: Self)
        ensures res.op == op
    {
        PendingOperation {
            op,
            resp: None,
        }
    }

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
    pub batch_perms: Option<PermissionOpt<PendingOperation>>,

    /// The flat combiner slot.
    /// XXX: somehow can't make this tracked?
    ///
    ///  - Dafny: glinear fc: FCSlot,
    pub slots: FlatCombiner::slots,

    /// tracks the update operation
    ///
    ///  - Dafny: glinear update: glOption<Update>
    pub update: Option<UnboundedLog::local_updates>
}

//  - Dafny: predicate inv(v: uint64, i: nat, cell: Cell<OpResponse>, fc_loc_s: nat)
pub open spec fn inv(&self, v: u64, tid: nat, cell: PCell<PendingOperation>, fc: FlatCombiner::Instance, inst: UnboundedLog::Instance) -> bool {
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
            &&& self.update.is_None()
            &&& self.batch_perms.is_None()
            // &&& self.batch_perms@@.value.is_None()
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
            &&& self.update.is_Some()
            &&& self.update.get_Some_0()@.value.is_Init()
            &&& self.update.get_Some_0()@.key == self.slots@.value.get_ReqId()
            &&& self.update.get_Some_0()@.instance == inst

            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_Some()
            &&& self.batch_perms.get_Some_0()@.pcell == cell.id()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().op == self.update.get_Some_0()@.value.get_Init_op()
        })

        // && (fc.state.FCInProgress? ==>
        //   && update.glNone?
        //   && contents.glNone?
        // )
        &&& (self.slots@.value.is_InProgress() ==> {
            &&& self.update.is_None()
            &&& self.batch_perms.is_None()
        })

        // && (fc.state.FCResponse? ==>
        //   && update.glSome?
        //   && update.value.us.UpdateDone?
        //   && update.value.rid == fc.state.rid
        //   && contents.glSome?
        //   && contents.value.cell == cell
        //   && contents.value.v.ret == update.value.us.ret
        // )
        &&& (self.slots@.value.is_Response() ==> {
            &&& self.update.is_Some()
            &&& self.update.get_Some_0()@.value.is_Done()
            &&& self.update.get_Some_0()@.key == self.slots@.value.get_ReqId()
            &&& self.update.get_Some_0()@.instance == inst

            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_Some()
            &&& self.batch_perms.get_Some_0()@.pcell == cell.id()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().resp.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().resp.get_Some_0() == self.update.get_Some_0()@.value.get_Done_ret()
        })
    }
}
} // struct_with_invariants! ContextGhost


/// Request Enqueue/Dequeue ghost state
pub tracked struct FCClientRequestResponseGhost {
    pub tracked batch_perms: Option<PermissionOpt<PendingOperation>>,
    pub tracked local_updates: Option<UnboundedLog::local_updates>,
    pub tracked fc_clients: FlatCombiner::clients
}

impl FCClientRequestResponseGhost {
    pub open spec fn enqueue_op_pre(&self, tid: nat, op: UpdateOp, batch_cell: CellId, fc_inst: FlatCombiner::Instance, inst: UnboundedLog::Instance) -> bool {
        &&& self.local_updates.is_Some()
        &&& self.local_updates.get_Some_0()@.instance == inst
        &&& self.local_updates.get_Some_0()@.value.is_Init()
        &&& self.local_updates.get_Some_0()@.value.get_Init_op() == op

        &&& self.batch_perms.is_Some()
        &&& self.batch_perms.get_Some_0()@.pcell == batch_cell
        &&& self.batch_perms.get_Some_0()@.value.is_None()

        &&& self.fc_clients@.instance == fc_inst
        &&& self.fc_clients@.key == tid
        &&& self.fc_clients@.value.is_Idle()
    }

    pub open spec fn enqueue_op_post(&self, pre: FCClientRequestResponseGhost) -> bool
        recommends pre.local_updates.is_Some()
    {
        &&& self.fc_clients@.value.is_Waiting()
        &&& self.fc_clients@.value.get_Waiting_0() == pre.local_updates.get_Some_0()@.key
        &&& self.fc_clients@.instance == pre.fc_clients@.instance
        &&& self.fc_clients@.key == pre.fc_clients@.key

        // the rest is none
        &&& self.batch_perms.is_None()
        &&& self.local_updates.is_None()
    }

    pub open spec fn dequeue_resp_pre(&self, tid: nat, fc_inst: FlatCombiner::Instance) -> bool {
        &&& self.batch_perms.is_None()
        &&& self.local_updates.is_None()

        &&& self.fc_clients@.key == tid
        &&& self.fc_clients@.instance == fc_inst
        &&& self.fc_clients@.value.is_Waiting()
    }

    pub open spec fn dequeue_resp_post(&self, pre: FCClientRequestResponseGhost, ret: Option<ReturnType>, inst: UnboundedLog::Instance) -> bool {
        &&& ret.is_Some() ==> {
            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_None()

            &&& self.local_updates.is_Some()
            &&& self.local_updates.get_Some_0()@.instance == inst
            &&& self.local_updates.get_Some_0()@.value.is_Done()
            &&& self.local_updates.get_Some_0()@.key == pre.fc_clients@.value.get_Waiting_0()
            &&& self.local_updates.get_Some_0()@.value.get_Done_ret() == ret.get_Some_0()

            &&& self.fc_clients@.instance == pre.fc_clients@.instance
            &&& self.fc_clients@.key == pre.fc_clients@.key
            &&& self.fc_clients@.value.is_Idle()
        }
        &&& ret.is_None() ==> {
            &&& self == pre
        }
    }
}




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
    pub thread_id_g: Ghost<nat>,
    // pub atomic_val: Ghost<nat>,

    /// ghost: the flat combiner instance
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
}

// XXX: in Dafny, this predicate takes the thread id and the flat combiner instance as arguments,
// but it seems that this is not possible here?
pub open spec fn wf(&self, thread_idx: nat) -> bool {
    predicate {
        self.thread_id_g@ == thread_idx
    }
    invariant on atomic with (flat_combiner_instance, unbounded_log_instance, batch, thread_id_g) specifically (self.atomic.0) is (v: u64, g: ContextGhost) {
        // (forall v, g :: atomic_inv(atomic.inner, v, g) <==> g.inv(v, i, cell.inner, fc_loc))
        // &&& atomic_val == v
        &&& g.inv(v, thread_id_g@, batch.0, flat_combiner_instance@, unbounded_log_instance@)
    }
}} // struct_with_invariants!

impl Context {

    pub fn new(thread_id: usize, slot: Tracked<FlatCombiner::slots>, flat_combiner_instance: Tracked<FlatCombiner::Instance>, unbounded_log_instance: Tracked<UnboundedLog::Instance>)
        -> (res: (Context, Tracked<PermissionOpt<PendingOperation>>))
        ensures
            res.0.wf(thread_id as nat),
            res.0.flat_combiner_instance == flat_combiner_instance,
            res.0.unbounded_log_instance == unbounded_log_instance,
            res.1@@.value.is_None()
     {
        let ghost mut thread_id_g;
        proof {
            thread_id_g = thread_id as nat;
        }

        //
        // create the storage for storing the update operation
        //
        let (batch, batch_perms) = PCell::empty();
        let batch = CachePadded(batch);
        //
        // create the ghost context
        //
        let tracked context_ghost = ContextGhost {
            batch_perms: None,
            slots: slot.get(),
            update: Option::None,
        };

        let atomic = AtomicU64::new((flat_combiner_instance, unbounded_log_instance, batch, ghost(thread_id_g)), 0, context_ghost);

        //
        // Assemble the context
        //

        (Context {
            batch: batch,
            atomic: CachePadded(atomic),
            thread_id_g: ghost(thread_id_g),
            flat_combiner_instance,
            unbounded_log_instance
        }, batch_perms)
    }

    /// Enqueues an operation onto this context's batch of pending operations.
    ///
    /// This is invoked by the thread that want's to execute an operation
    ///
    /// Note, enqueue is a bit a misnomer. We just have one operation per thread
    pub fn enqueue_op(&self, op: UpdateOp, context_ghost: Tracked<FCClientRequestResponseGhost>)
        -> (res: (bool, Tracked<FCClientRequestResponseGhost>))
        requires
            context_ghost@.enqueue_op_pre(self.thread_id_g@, op, self.batch.0.id(), self.flat_combiner_instance@, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
            // self.atomic_val == 0
        ensures
            res.1@.enqueue_op_post(context_ghost@),
            self.wf(self.thread_id_g@),
            // self.atomic_val == 1
    {
        let tracked FCClientRequestResponseGhost { batch_perms, local_updates, mut fc_clients } = context_ghost.get();

        let mut batch_perms = tracked(batch_perms.tracked_unwrap());
        let tracked local_updates = local_updates.tracked_unwrap();

        // put the operation there, updates the permissions so we can store them in the GhostContext
        self.batch.0.put(&mut batch_perms, PendingOperation::new(op));

        let tracked send_request_result;
        let res = atomic_with_ghost!(
            &self.atomic.0 => store(1);
            update prev->next;
            ghost g => {
                let ghost tid = fc_clients.view().key;
                let ghost rid = local_updates.view().key;

                self.flat_combiner_instance.borrow().pre_send_request(tid, &fc_clients, &g.slots);
                send_request_result = self.flat_combiner_instance.borrow().send_request(tid, rid, fc_clients, g.slots);
                // update the flat combiner clients
                fc_clients = send_request_result.0.0;

                // update the ghost context
                g.slots = send_request_result.1.0;
                g.batch_perms = Some(batch_perms.get());
                g.update = Some(local_updates);

                assert(g.inv(1, tid, self.batch.0, self.flat_combiner_instance.view(), self.unbounded_log_instance.view()))
            }
        );

        let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms: None, local_updates: None, fc_clients };
        (true, tracked(new_context_ghost))
    }


    /// Returns a single response if available. Otherwise, returns None.
    ///
    /// this is invoked by the thread that has enqueued the operation before
    pub fn dequeue_response(&self, context_ghost: Tracked<FCClientRequestResponseGhost>)
        -> (res: (Option<ReturnType>, Tracked<FCClientRequestResponseGhost>))
        requires
            context_ghost@.dequeue_resp_pre(self.thread_id_g@, self.flat_combiner_instance@),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, res.0, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost { mut batch_perms, mut local_updates, mut fc_clients } = context_ghost.get();

        let tracked recv_response_result;
        let res = atomic_with_ghost!(
            &self.atomic.0 => load();
            returning res;
            ghost g => {
                if res == 0 {
                    // TODO: if we call this function we should be waiting for a response,
                    batch_perms = g.batch_perms;
                    local_updates = g.update;

                    let tid = fc_clients.view().key;
                    let rid = fc_clients.view().value.get_Waiting_0();

                    self.flat_combiner_instance.borrow().pre_recv_response(tid, &fc_clients, &g.slots);

                    assert(g.slots.view().value.is_Response());
                    assert(g.slots.view().value.get_Response_0() == rid);

                    assert(fc_clients.view().value.get_Waiting_0() == local_updates.get_Some_0().view().key);

                    recv_response_result = self.flat_combiner_instance.borrow().recv_response(tid, rid, fc_clients, g.slots);

                    fc_clients = recv_response_result.0.0;
                    g.slots = recv_response_result.1.0;
                    g.batch_perms = None;
                    g.update = None;
                }
            }
        );

        if res == 0 {
            let mut batch_perms = tracked(batch_perms.tracked_unwrap());

            let op = self.batch.0.take(&mut batch_perms);

            let resp = op.resp.unwrap();
            let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms: Some(batch_perms.get()), local_updates, fc_clients };
            (Some(resp), tracked(new_context_ghost))
        } else {
            let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms, local_updates, fc_clients };
            (None, tracked(new_context_ghost))
        }
    }


    /// Enqueues a response onto this context. This is invoked by the combiner
    /// after it has executed operations (obtained through a call to ops()) against the
    /// replica this thread is registered against.
    pub fn enqueue_response(&self, resp: ReturnType) -> bool
        requires
            self.wf(self.thread_id_g@)
            // self.atomic != 0
    {
        // let tracked token : Option<Tracked<PermissionOpt<PendingOperation>>>;
        // let res = atomic_with_ghost!(
        //     &self.atomic.0 => load();
        //     returning res;
        //     ghost g => {
        //         if res == 1 {
        //             // store the operatin in the cell
        //             token =  Some(g.batch_perms);
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
    pub data: DataStructureType,
    // TODO: add the ghost replica here!
    ///  - Dafny: glinear ghost_replica: Replica,
    pub replica: Tracked<UnboundedLog::replicas>,
    ///  - Dafny: glinear combiner: CombinerToken,
    pub combiner: Tracked<UnboundedLog::combiner>,
    ///  - Dafny: glinear cb: CBCombinerToken
    pub cb_combiner: Tracked<CyclicBuffer::combiner>
}

//  - Dafny: predicate WF(nodeId: nat, cb_loc_s: nat) {
pub open spec fn wf(&self, nid: NodeId, inst: UnboundedLog::Instance, cb: CyclicBuffer::Instance) -> bool {
    predicate {
        // combiner instance
        &&& self.combiner@@.instance == inst
        &&& self.replica@@.instance == inst

        // && ghost_replica.state == nrifc.I(actual_replica)
        &&& self.replica@@.value == self.data.interp()
        // && ghost_replica.nodeId == nodeId
        &&& self.replica@@.key == nid
        // && combiner.state == CombinerReady
        &&& self.combiner@@.value.is_Ready()
        // && combiner.nodeId == nodeId
        &&& self.combiner@@.key == nid
        // && cb.nodeId == nodeId
        &&& self.cb_combiner@@.key == nid
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
    pub flat_combiner: Tracked<FlatCombiner::combiner>,

    /// Stores the token to access the collected_operations in the replica
    ///  - Dafny: glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>,
    pub collected_operations_perm: Tracked<PermissionOpt<Vec<UpdateOp>>>,

    /// Stores the token to access the number of collected operations in the replica
    pub collected_operations_per_thread_perm: Tracked<PermissionOpt<Vec<usize>>>,

    /// Stores the token to access the responses in teh Replica
    ///  - Dafny: glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>,
    pub responses_token: Tracked<PermissionOpt<Vec<ReturnType>>>,
}

//  - Dafny: predicate CombinerLockInv(v: uint64, g: glOption<CombinerLockState>, fc_loc: nat,
//                                     ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
//                                     responses: LC.LinearCell<seq<nrifc.ReturnType>>)
//
// Note: this predicate only holds when the lock is not taken.
pub open spec fn inv(&self, combiner_instance: FlatCombiner::Instance, responses_id: CellId, op_buffer_id: CellId, thread_ops: CellId) -> bool {
    predicate {
        // && g.value.flatCombiner.state == FC.FCCombinerCollecting([])
        &&& self.flat_combiner@@.value.is_Collecting()
        &&& self.flat_combiner@@.value.get_Collecting_0().len() == 0

        // && g.value.flatCombiner.loc_s == fc_loc
        &&& self.flat_combiner@@.instance == combiner_instance

        // && g.value.gops.v.Some?
        &&& self.collected_operations_perm@@.value.is_Some()

        // && g.value.gresponses.lcell == responses
        &&& self.collected_operations_perm@@.pcell == op_buffer_id

        // && |g.value.gops.v.value| == MAX_THREADS_PER_REPLICA as int
        &&& self.collected_operations_perm@@.value.get_Some_0().len() == 0 // we use vector push MAX_THREADS_PER_REPLICA

        // && g.value.gresponses.v.Some?
        &&& self.responses_token@@.value.is_Some()

        // && g.value.gops.lcell == ops
        &&& self.responses_token@@.pcell == responses_id

        // && |g.value.gresponses.v.value| == MAX_THREADS_PER_REPLICA as int
        &&& self.responses_token@@.value.get_Some_0().len() == 0 // we use vector push MAX_THREADS_PER_REPLICA

        &&& self.collected_operations_per_thread_perm@@.value.is_Some()
        &&& self.collected_operations_per_thread_perm@@.pcell == thread_ops
        &&& self.collected_operations_per_thread_perm@@.value.get_Some_0().len() == 0
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
    pub collected_operations: PCell<Vec<UpdateOp>>,


    // /// Number of operations collected by the combiner from each thread at any
    // we just have one inflight operation per thread
    // inflight: RefCell<[usize; MAX_THREADS_PER_REPLICA]>,
    pub collected_operations_per_thread: PCell<Vec<usize>>,

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
    pub data: CachePadded<RwLock<ReplicatedDataStructure>>,


    /// Thread index that will be handed out to the next thread that registers
    // with the replica when calling [`Replica::register()`].
    // next: CachePadded<AtomicU64<_, FlatCombiner::num_threads, _>>,
    // thread token that is handed out to the threads that register
    pub (crate) thread_tokens: Vec<ThreadToken>,



    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

pub open spec fn wf(&self) -> bool {

    predicate {
        // && (forall i | 0 <= i < |contexts| :: i in contexts && contexts[i].WF(i, fc_loc))
        &&& (forall |i: int| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i]).wf(i as nat))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).flat_combiner_instance == self.flat_combiner_instance)
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).unbounded_log_instance == self.unbounded_log_instance)

        // && |contexts| == MAX_THREADS_PER_REPLICA as int
        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        // && 0 <= nodeId as int < NUM_REPLICAS as int
        &&& 0 <= self.spec_id() < NUM_REPLICAS
        // && replica.InternalInv()
        &&& self.data.0.wf()
        // &&& self.data.0.internal_inv()
        // TODO: is this the right way to do this?
        &&& (forall |v: ReplicatedDataStructure| #[trigger] self.data.0.inv(v) == v.wf(self.spec_id(), self.unbounded_log_instance@, self.cyclic_buffer_instance@))

        // XXX: the number of threads must agree here!, make this dynamic?
        &&& self.flat_combiner_instance@.num_threads() == MAX_THREADS_PER_REPLICA

        &&& (forall |i| #![trigger self.thread_tokens[i]] 0 <= i < self.thread_tokens.len() ==> {
            self.thread_tokens[i].wf()
        })

        // XXX: What is that one here???
        // seems to refer to module NodeReplica(nrifc: NRIfc) refines ContentsTypeMod
        // of the actual replica wrapping the data structure?
        //&& (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int, nr.cb_loc_s))
    }

    // (forall v, g :: atomic_inv(combiner_lock.inner, v, g) <==> CombinerLockInv(v, g, fc_loc, ops, responses))
    invariant on combiner with (flat_combiner_instance, responses, collected_operations, collected_operations_per_thread) specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost>) {
        // v != means lock is not taken,
        &&& (v == 0) <==> g.is_Some()
        // the lock is not taken, the ghost state is Some
        &&& (g.is_Some() ==> g.get_Some_0().inv(flat_combiner_instance@, responses.id(), collected_operations.id(), collected_operations_per_thread.id()))
    }

    // invariant on next specifically (self.next.0) is (v: u64, g: FlatCombiner::num_threads) {
    //     &&& 0 <= v < MAX_THREADS_PER_REPLICA
    //     &&& v == g
    // }
}

} // struct_with_invariants!

struct ThreadOpsData {
    flat_combiner: Tracked<FlatCombiner::combiner>,
    request_ids: Ghost<Seq<ReqId>>,
    local_updates: Tracked<Map<nat, UnboundedLog::local_updates>>,
    cell_permissions: Tracked<Map<nat, PermissionOpt<PendingOperation>>>,
}

impl ThreadOpsData {
    spec fn shared_inv(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>, num_ops_per_thread: Seq<usize>,
                       replica_contexts: Seq<Context>) -> bool {
        &&& self.flat_combiner@@.instance == flat_combiner_instance@
        &&& self.flat_combiner@@.value.is_Responding()
        &&& self.flat_combiner@@.value.get_Responding_0().len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& num_ops_per_thread.len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& self.flat_combiner@@.value.get_Responding_1() == 0

        &&& (forall|i: nat|
           #![trigger num_ops_per_thread[i as int]]
           #![trigger self.flat_combiner@@.value.get_Responding_0()[i as int]]
            i < self.flat_combiner@@.value.get_Responding_0().len() ==> {
            &&& num_ops_per_thread[i as int] > 0 == self.flat_combiner@@.value.get_Responding_0()[i as int].is_Some()
            &&& self.flat_combiner@@.value.get_Responding_0()[i as int].is_Some() ==> {
                &&& self.cell_permissions@.contains_key(i)
                &&& self.cell_permissions@[i]@.pcell === replica_contexts[i as int].batch.0.id()
                &&& self.cell_permissions@[i]@.value.is_Some()
            }
        })

    }

    spec fn distribute_thread_resps_pre(&self, flat_combiner_instance: Tracked<FlatCombiner::Instance>,
                                        unbounded_log_instance: UnboundedLog::Instance,
                                        num_ops_per_thread: Seq<usize>, responses: Seq<ReturnType>,
                                        replica_contexts: Seq<Context>) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)

        // &&& responses.len() == MAX_THREADS_PER_REPLICA
        &&& self.request_ids@.len() == responses.len()
        // TODO: why does that need to be separate?
        &&& (forall |i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
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
                unbounded_log_instance: UnboundedLog::Instance, num_ops_per_thread: Seq<usize>,
                operations: Seq<UpdateOp>, replica_contexts: Seq<Context>) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)
        &&& self.request_ids@.len() == operations.len()
        // TODO; why does that need to be separate?
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


/// struct containing arguments for creating a new replica
pub tracked struct ReplicaConfig {
    pub tracked replicas: UnboundedLog::replicas,
    pub tracked combiner: UnboundedLog::combiner,
    pub tracked cb_combiner: CyclicBuffer::combiner,
    pub tracked unbounded_log_instance: UnboundedLog::Instance,
    pub tracked cyclic_buffer_instance: CyclicBuffer::Instance,
}

impl ReplicaConfig {
    pub open spec fn wf(&self, nid: nat) -> bool {
        &&& self.combiner@.instance == self.unbounded_log_instance
        &&& self.cb_combiner@.instance == self.cyclic_buffer_instance

        &&& self.replicas@.value == DataStructureSpec::init()
        &&& self.replicas@.key == nid
        &&& self.replicas@.instance == self.unbounded_log_instance
        &&& self.combiner@.value.is_Ready()
        &&& self.combiner@.key == nid
        &&& self.cb_combiner@.key == nid
        &&& self.cb_combiner@.value.is_Idle()
        &&& self.cb_combiner@.instance == self.cyclic_buffer_instance
    }
}

impl Replica  {

    // needs some kind of ghost state
    pub fn new(replica_token: ReplicaToken, num_threads: usize, config: Tracked<ReplicaConfig>) -> (res: Self)
        requires
            num_threads == MAX_THREADS_PER_REPLICA,
            replica_token.id_spec() < NUM_REPLICAS,
            config@.wf(replica_token.id_spec())
        ensures
            res.wf()
    {
        let tracked ReplicaConfig {
            replicas,
            combiner,
            cb_combiner,
            unbounded_log_instance,
            cyclic_buffer_instance,
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
                Trk(fc_instance0), // FlatCombiner::Instance,
                Trk(fc_clients0),  // Map<ThreadId, FlatCombiner::clients>,
                Trk(fc_slots0),    // Map<ThreadId, FlatCombiner::slots>,
                Trk(fc_combiner0), // FlatCombiner::combiner
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
            data: DataStructureType::init(),
            replica: tracked(replicas),
            combiner: tracked(combiner),
            cb_combiner: tracked(cb_combiner)
        };
        assert(replicated_data_structure.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance));
        // TODO: get the right spec function in there!
        let ghost data_structure_inv = closure_to_fn_spec(|s: ReplicatedDataStructure| {
            s.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance)
        });
        let data = CachePadded(RwLock::new(replicated_data_structure, ghost(data_structure_inv)));

        //
        // Create the thread contexts
        //
        let mut contexts : Vec<Context> = Vec::with_capacity(num_threads);
        let mut thread_tokens : Vec<ThreadToken> = Vec::with_capacity(num_threads);

        let mut idx = 0;
        while idx < num_threads
            invariant
                num_threads <= MAX_THREADS_PER_REPLICA,
                replica_token.id_spec() < NUM_REPLICAS,
                contexts.len() == idx,
                thread_tokens.len() == idx,
                0 <= idx <= num_threads,
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
                    thread_tokens[i].wf()
                }
        {
            let tracked slot;
            let tracked client;
            proof {
                slot = fc_slots.tracked_remove(idx as nat);
                client = fc_clients.tracked_remove(idx as nat);
            }
            let fc_inst = tracked(fc_instance.clone());
            let ul_inst = tracked(unbounded_log_instance.clone());

            let (context, batch_perm) = Context::new(idx, tracked(slot), fc_inst, ul_inst);
            contexts.push(context);

            let token = ThreadToken {
                rid: replica_token.clone(),
                tid: idx as u32,
                fc_client: tracked(client),
                batch_perm
            };

            thread_tokens.push(
                token
            );

            idx = idx + 1;
        }

        let tracked context_ghost = CombinerLockStateGhost {
            flat_combiner: tracked(fc_combiner),
            collected_operations_perm,
            collected_operations_per_thread_perm,
            responses_token,
        };

        let fc_inst = tracked(fc_instance.clone());
        let combiner = CachePadded(AtomicU64::new((fc_inst, responses, collected_operations, collected_operations_per_thread), 0, Option::Some(context_ghost)));

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
            unbounded_log_instance: tracked(unbounded_log_instance),
            cyclic_buffer_instance: tracked(cyclic_buffer_instance),
            flat_combiner_instance: tracked(fc_instance),
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
    fn acquire_combiner_lock(&self) -> (result: (bool, Tracked<Option<CombinerLockStateGhost>>))
        requires self.wf()
        ensures
          result.0 ==> result.1@.is_Some(),
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
            (val == 0, tracked(lock_g))
        } else {
            (false, tracked(None))
        }
    }

    fn release_combiner_lock(&self, lock_state: Tracked<CombinerLockStateGhost>)
        requires
            self.wf(),
            lock_state@.inv(self.flat_combiner_instance@, self.responses.id(), self.collected_operations.id(), self.collected_operations_per_thread.id()),
    {
        atomic_with_ghost!(
            &self.combiner.0 => store(0);
            update old_val -> new_val;
            ghost g
            => {
                // assert(old_val == v);
                // assert(old_val != 0);
                // assert(g.is_None());
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
          slog.wf(),
          self.unbounded_log_instance@ == slog.unbounded_log_instance@,
          slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
    {
        // Step 1: try to take the combiner lock to become combiner
        let (acquired, combiner_lock) = self.acquire_combiner_lock();

        // Step 2: if we are the combiner then perform flat combining, else return
        if acquired {
            assert(combiner_lock@.is_Some());
            let combiner_lock = tracked(combiner_lock.get().tracked_unwrap());
            let combiner_lock = self.combine(slog, combiner_lock);
            self.release_combiner_lock(combiner_lock);
        } else {
            // nothing to be done here.
        }
    }

    /// Performs one round of flat combining. Collects, appends and executes operations.
    ///
    /// https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/nr/replica.rs#L835
    fn combine(&self, slog: &NrLog, combiner_lock: Tracked<CombinerLockStateGhost>)
            -> (result: Tracked<CombinerLockStateGhost>)
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
        let flat_combiner = tracked_exec(combiner_lock.flat_combiner.get());
        let mut collected_operations_perm = tracked_exec(combiner_lock.collected_operations_perm.get());
        let mut collected_operations_per_thread_perm = tracked_exec(combiner_lock.collected_operations_per_thread_perm.get());
        let mut responses_token = tracked_exec(combiner_lock.responses_token.get());

        // obtain access to the responses, operations and num_ops_per_thread buffers
        let mut responses = self.responses.take(&mut responses_token);

        let mut operations = self.collected_operations.take(&mut collected_operations_perm);

        assert(self.collected_operations_per_thread.id() == collected_operations_per_thread_perm@@.pcell);
        let mut num_ops_per_thread = self.collected_operations_per_thread.take(&mut collected_operations_per_thread_perm);

        // Step 1: collect the operations from the threads
        // self.collect_thread_ops(&mut buffer, operations.as_mut_slice());

        let collect_res = self.collect_thread_ops(&mut operations, &mut num_ops_per_thread, flat_combiner);
        let tracked collect_res = collect_res.get();
        let flat_combiner = tracked_exec(collect_res.flat_combiner.get());
        let local_updates = tracked_exec(collect_res.local_updates.get());
        let request_ids :  Ghost<Seq<ReqId>> = ghost_exec(collect_res.request_ids@);
        let cell_permissions = tracked_exec(collect_res.cell_permissions.get());

        // flat_combiner: Tracked<FlatCombiner::combiner>,
        // request_ids: Ghost<Seq<ReqId>>,
        // local_updates: Tracked<Map<nat, UnboundedLog::local_updates>>,
        // cell_permissions: Tracked<Map<nat, PermissionOpt<PendingOperation>>>,

        // Step 2: Take the R/W lock on the data structure
        let (replicated_data_structure, write_handle) = self.data.0.acquire_write();
        let mut data = replicated_data_structure.data;
        let ghost_replica = replicated_data_structure.replica;
        let combiner = replicated_data_structure.combiner;
        let cb_combiner = replicated_data_structure.cb_combiner;

        let tracked append_exec_ghost_data = NrLogAppendExecDataGhost {
            local_updates ,
            ghost_replica ,
            combiner ,
            cb_combiner ,
            request_ids ,
        };

        // Step 3: Append all operations to the log

        assert(append_exec_ghost_data.append_pre(operations@, self.replica_token@, self.unbounded_log_instance@, self.cyclic_buffer_instance@));

        assert(forall |i|  #[trigger] append_exec_ghost_data.local_updates@.contains_key(i) ==> {
            &&& (#[trigger] append_exec_ghost_data.local_updates@[i])@.instance == self.unbounded_log_instance@}
        );

        let append_exec_ghost_data = slog.append(&self.replica_token, &operations, &responses, tracked(append_exec_ghost_data));

        // Step 3: Execute all operations
        assert(append_exec_ghost_data@.execute_pre(self.replica_token@, self.unbounded_log_instance@, self.cyclic_buffer_instance@));
        let tracked append_exec_ghost_data = slog.execute(&self.replica_token, &mut responses, &mut data, append_exec_ghost_data);

        let tracked NrLogAppendExecDataGhost {
            local_updates ,
            ghost_replica ,
            combiner ,
            cb_combiner ,
            request_ids ,
        } = append_exec_ghost_data.get();

        // Step 4: release the R/W lock on the data structure
        // let replicated_data_structure = ReplicatedDataStructure  { data, replica: ghost_replica, combiner, cb_combiner };
        // self.data.0.release_write(replicated_data_structure, write_handle);

        // // Step 5: collect the results
        let tracked thread_ops_data = ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions };

        assert(thread_ops_data.distribute_thread_resps_pre(self.flat_combiner_instance, self.unbounded_log_instance@, num_ops_per_thread@, responses@, self.contexts@));
        let distribute_thread_resps_result = self.distribute_thread_resps(&mut responses, &mut num_ops_per_thread, tracked(thread_ops_data));

        let tracked ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions } = distribute_thread_resps_result.get();

        // clear the buffers again
        responses.clear();
        operations.clear();
        num_ops_per_thread.clear();

        // // place the responses back into the state
        self.responses.put(&mut responses_token, responses);
        self.collected_operations.put(&mut collected_operations_perm, operations);
        self.collected_operations_per_thread.put(&mut collected_operations_per_thread_perm, num_ops_per_thread);

        // re-assemble the combiner lock
        let tracked combiner_lock =  CombinerLockStateGhost { flat_combiner, collected_operations_perm, collected_operations_per_thread_perm, responses_token };
        tracked(combiner_lock)
    }

    ///
    /// - Dafny: combine_collect()
    #[inline(always)]
    fn collect_thread_ops(&self, operations: &mut Vec<UpdateOp>, num_ops_per_thread: &mut Vec<usize>,
                          flat_combiner:  Tracked<FlatCombiner::combiner>)
                             -> (response: Tracked<ThreadOpsData>)
        requires
            self.wf(),
            old(num_ops_per_thread).len() == 0,
            old(operations).len() == 0,
            // requires flatCombiner.loc_s == node.fc_loc
            flat_combiner@@.instance == self.flat_combiner_instance@,
            // requires flatCombiner.state == FC.FCCombinerCollecting([])
            flat_combiner@@.value.is_Collecting(),
            flat_combiner@@.value.get_Collecting_0().len() == 0,
        ensures
            operations.len() <= MAX_REQUESTS,
            response@.collect_thread_ops_post(self.flat_combiner_instance, self.unbounded_log_instance@, num_ops_per_thread@, operations@, self.contexts@)
    {
        let mut flat_combiner = flat_combiner;

        let tracked mut updates: Map<nat, UnboundedLog::local_updates> = Map::tracked_empty();
        let tracked mut cell_permissions: Map<nat, PermissionOpt<PendingOperation>> = Map::tracked_empty();
        let ghost mut request_ids = Seq::empty();


        assert(rids_match(flat_combiner@@.value.get_Collecting_0(), request_ids,
        0, flat_combiner@@.value.get_Collecting_0().len(), 0, request_ids.len()));

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
                    num_ops_per_thread[i as int] > 0 ==
                    (#[trigger] flat_combiner@@.value.get_Collecting_0()[i as int]).is_Some(),
                forall |i: nat| i < flat_combiner@@.value.get_Collecting_0().len() &&
                    (#[trigger] flat_combiner@@.value.get_Collecting_0()[i as int]).is_Some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i]@.value.is_Some()
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
            assert(self.contexts.spec_index(thread_idx as int).wf(thread_idx as nat));
            assert(self.contexts.spec_index(thread_idx as int).thread_id_g == thread_idx as nat);

            let tracked update_req : Option<UnboundedLog::local_updates>;
            let tracked batch_perms : Option<PermissionOpt<PendingOperation>>;
            // let tracked

            let num_ops = atomic_with_ghost!(
                &self.contexts.index(thread_idx).atomic.0 => load();
                returning num_ops;
                ghost g // g : ContextGhost
            => {
                assert(flat_combiner.view().view().value.get_Collecting_0().len() == thread_idx);

                if num_ops == 1 {
                    self.flat_combiner_instance.borrow().pre_combiner_collect_request(&g.slots, flat_combiner.borrow());

                    assert(g.slots.view().value.is_Request());
                    rids_match_add_rid(flat_combiner.view().view().value.get_Collecting_0(), request_ids,
                        0, flat_combiner.view().view().value.get_Collecting_0().len(), 0, request_ids.len(),g.update.get_Some_0().view().key);

                    g.slots = self.flat_combiner_instance.borrow().combiner_collect_request(g.slots, flat_combiner.borrow_mut());
                    update_req = g.update;
                    batch_perms = g.batch_perms;
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
                assert(batch_perms.is_Some());
                assert(update_req.is_Some());
                // reading the op cell
                let batch_token_value = tracked(batch_perms.tracked_unwrap());
                let op = self.contexts.index(thread_idx).batch.0.borrow(&batch_token_value).op.clone();

                let tracked update_req = update_req.tracked_unwrap();
                assert(update_req@.instance == self.unbounded_log_instance);
                assert(update_req@.value.is_Init());
                assert(update_req@.value.get_Init_op() == op);
                proof {
                    updates.tracked_insert(request_ids.len() as nat, update_req);
                    cell_permissions.tracked_insert(thread_idx as nat, batch_token_value.get());
                }

                // assert(operations.len() == request_ids.len());
                request_ids = request_ids.push(update_req@.key);
                operations.push(op);
            } else {
                // nothing here
                // assert(operations.len() == request_ids.len());
            }

            // set the number of active operations per thread
            num_ops_per_thread.push(num_ops as usize);

            thread_idx = thread_idx + 1;
        }

        assert(flat_combiner@@.value.get_Collecting_0().len() == num_registered_threads);

        self.flat_combiner_instance.borrow().combiner_responding_start(flat_combiner.borrow_mut());

        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner,
            request_ids: ghost(request_ids),
            local_updates: tracked(updates),
            cell_permissions: tracked(cell_permissions)
        };
        tracked(thread_ops_data)
    }

    ///
    /// - Dafny: combine_respond
    fn distribute_thread_resps(&self, responses: &mut Vec<ReturnType>, num_ops_per_thread: &mut Vec<usize>, thread_ops_data: Tracked<ThreadOpsData>)
        -> (res: Tracked<ThreadOpsData>)
        requires
            self.wf(),
            thread_ops_data@.distribute_thread_resps_pre(self.flat_combiner_instance, self.unbounded_log_instance@, old(num_ops_per_thread)@, old(responses)@, self.contexts@),
            rids_match(thread_ops_data@.flat_combiner@@.value.get_Responding_0(), thread_ops_data@.request_ids@,
                0, thread_ops_data@.flat_combiner@@.value.get_Responding_0().len(), 0, thread_ops_data@.request_ids@.len())
        ensures
            res@.distribute_thread_resps_post(self.flat_combiner_instance)

    {
        let tracked ThreadOpsData {
            flat_combiner,
            request_ids,
            local_updates,
            cell_permissions,
        } = thread_ops_data.get();
        let tracked mut flat_combiner = flat_combiner.get();
        let tracked mut cell_permissions = cell_permissions.get();
        let tracked mut updates = local_updates.get();


        // let num_registered_threads = self.next.load(Ordering::Relaxed);
        let num_registered_threads = MAX_THREADS_PER_REPLICA;

        // TODO: not sure why this one here is needed?. it comes from the pre-conditin
        assert(forall|i: nat| #![trigger updates[i]] 0 <= i < request_ids@.len() ==> updates.contains_key(i));
        // TODO: that's literally from the `wf()`, why does that fail?
        assert(self.flat_combiner_instance@.num_threads() == num_registered_threads);

        // let (mut s, mut f) = (0, 0);
        // for i in 1..num_registered_threads {
        let mut thread_idx = 0;
        let mut resp_idx : usize = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                0 <= resp_idx <= responses.len(),
                resp_idx <= thread_idx,
                // thread_idx < num_registered_threads ==> resp_idx < responses.len(), // TODO do we actually need this?
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
                    num_ops_per_thread[i as int] > 0 ==
                    (#[trigger] flat_combiner@.value.get_Responding_0()[i as int]).is_Some(),
                forall |i: nat| thread_idx <= i < flat_combiner@.value.get_Responding_0().len() &&
                    (#[trigger] flat_combiner@.value.get_Responding_0()[i as int]).is_Some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i]@.value.is_Some()
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
                // thread_idx as nat <= flat_combiner@.value.get_Responding_0().len(),
                rids_match(flat_combiner@.value.get_Responding_0(), request_ids@,
                    thread_idx as nat, flat_combiner@.value.get_Responding_0().len(),
                    resp_idx as nat, request_ids@.len()),

        {

            proof {
                rids_match_pop(flat_combiner@.value.get_Responding_0(), request_ids@,
                    thread_idx as nat, flat_combiner@.value.get_Responding_0().len(),
                    resp_idx as nat, request_ids@.len());
            }

            let num_ops = *num_ops_per_thread.index(thread_idx);

            assert(flat_combiner@.value.get_Responding_1() < num_registered_threads);

            if num_ops == 0 {
                // if operations[i - 1] == 0 {
                //     continue;
                // };
                self.flat_combiner_instance.borrow().combiner_responding_empty(&mut flat_combiner);

                assert(forall|i: nat| #![trigger updates[i]] resp_idx <= i < request_ids@.len() ==> {
                    &&& updates.contains_key(i)
                });

            } else {

                //     f += operations[i - 1];
                //     self.contexts[i - 1].enqueue_resps(&results[s..f]);
                //     s += operations[i - 1];

                // obtain the element from the operation batch

                let mut permission: Tracked<_> = tracked(cell_permissions.tracked_remove(thread_idx as nat));
                let mut op_resp = self.contexts.index(thread_idx).batch.0.take(&mut permission);

                // update with the response
                let resp: ReturnType = responses.index(resp_idx).clone();
                op_resp.resp = Some(resp);
                // place the element back into the batch
                self.contexts.index(thread_idx).batch.0.put(&mut permission, op_resp);

                //     operations[i - 1] = 0;
                atomic_with_ghost!(
                    &self.contexts.index(thread_idx).atomic.0 => store(0);
                    update prev -> next;
                    ghost g // g : ContextGhost
                    => {
                        // record the pre-states of the transition values
                        g.slots = self.flat_combiner_instance.borrow().combiner_responding_result(g.slots, &mut flat_combiner);
                        g.batch_perms = Some(permission.get());
                        g.update = Some(updates.tracked_remove(resp_idx as nat));
                    }
                );

                resp_idx = resp_idx + 1;
            }

            thread_idx = thread_idx + 1;
        }

        self.flat_combiner_instance.borrow().combiner_responding_done(&mut flat_combiner);

        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner: tracked(flat_combiner),
            request_ids,
            local_updates: tracked(updates),
            cell_permissions : tracked(cell_permissions),
        };

        tracked(thread_ops_data)
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
    pub fn execute(&self, slog: &NrLog, op: ReadonlyOp, tkn: ThreadToken) -> Result<(ReturnType, ThreadToken), ThreadToken>
        requires
            self.wf(),
            slog.wf(),
            tkn.wf(),
            self.replica_token == tkn.rid,
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@
    {
        let tracked local_reads : UnboundedLog::local_reads;
        proof {
            // start the read transaction, get the ticket
            // (Gho<Map<ReqId,ReadonlyState>>, Trk<local_reads>, Gho<Map<NodeId,CombinerState>>)
            let tracked ticket = self.unbounded_log_instance.borrow().readonly_start(op);
            local_reads = ticket.1.0;
        }
        let ghost rid = local_reads@.key;
        let ghost nid = tkn.replica_id_spec();
        assert(nid == self.spec_id());


        // Step 1: Read the local tail value
        // let ctail = slog.get_ctail();
        let (version_upper_bound, local_reads) = slog.get_version_upper_bound(tracked(local_reads));

        // Step 2: wait until the replica is synced for reads, try to combine in mean time
        // while !slog.is_replica_synced_for_reads(&self.log_tkn, ctail) {
        //     if let Err(e) = self.try_combine(slog) {
        //         return Err((e, op));
        //     }
        //     spin_loop();
        // }
        let (mut is_synced, mut local_reads) = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, local_reads);
        while !is_synced
            invariant
                self.wf(),
                slog.wf(),
                !is_synced ==> local_reads@@.value.is_VersionUpperBound(),
                !is_synced ==> local_reads@@.value.get_VersionUpperBound_version_upper_bound() == version_upper_bound,
                !is_synced ==> local_reads@@.value.get_VersionUpperBound_op() == op,
                is_synced ==> local_reads@@.value.is_ReadyToRead(),
                is_synced ==> local_reads@@.value.get_ReadyToRead_node_id() == self.spec_id(),
                is_synced ==> local_reads@@.value.get_ReadyToRead_op() == op,
                local_reads@@.instance == self.unbounded_log_instance@,
                local_reads@@.key == rid,
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,

        {
            self.try_combine(slog);
            spin_loop_hint();
            let res = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, local_reads);
            is_synced = res.0;
            local_reads = res.1;
        }
        let tracked local_reads = local_reads.get();

        // Step 3: Take the read-only lock, and read the value
        // let res = self.data.read(idx.tid() - 1).dispatch(op)
        let read_handle = self.data.0.acquire_read();
        let replica = self.data.0.borrow(&read_handle);

        assert(replica.wf(nid, self.unbounded_log_instance@, self.cyclic_buffer_instance@));

        let result = replica.data.read(op);
        assert(result == replica.replica@@.value.spec_read(op));

        let tracked local_reads = self.unbounded_log_instance.borrow().readonly_apply(rid, replica.replica.borrow(), local_reads, replica.combiner.borrow());
        self.data.0.release_read(read_handle);

        // Step 4: Finish the read-only transaction, return result
        let tracked local_reads = local_reads;
        assert(local_reads@.value.get_Done_ret() == result);
        self.unbounded_log_instance.borrow().readonly_finish(rid, op, result, local_reads);

        // assert(false);
        Err(tkn)
    }

    /// Executes a mutable operation against this replica and returns a
    /// response.
    ///
    /// In Dafny this refers to do_operation
    pub fn execute_mut(&self, slog: &NrLog, op: UpdateOp, tkn: ThreadToken) -> (result: Result<(ReturnType, ThreadToken), ThreadToken>)
        requires
            slog.wf(),
            self.wf(),
            tkn.wf(),
            self.replica_token == tkn.rid,
            tkn.fc_client@@.instance == self.flat_combiner_instance@,
            tkn.batch_perm@@.pcell == self.contexts.spec_index(tkn.tid as int).batch.0.id(),
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@
        ensures
            result.is_Ok() ==> result.get_Ok_0().1.wf(),
            result.is_Err() ==> result.get_Err_0().wf()
    {
        // start the update transaction
        let tracked local_updates : UnboundedLog::local_updates;
        proof {
            //: (Gho<Map<ReqId, UpdateState>>, Trk<UnboundedLog::local_updates>, Gho<Map<NodeId, CombinerState>>)
            let tracked ticket = self.unbounded_log_instance.borrow().update_start(op);
            local_updates = ticket.1.0;
        }
        let ghost req_id = local_updates@.key;

        let ThreadToken { rid, tid, fc_client, batch_perm } = tkn;

        // Step 1: Enqueue the operation onto the thread local batch
        // while !self.make_pending(op.clone(), idx.tid()) {}
        // Note: if we have the thread token, this will always succeed.

        let tracked context_ghost = FCClientRequestResponseGhost { batch_perms: Some(batch_perm.get()), local_updates: Some(local_updates), fc_clients: fc_client.get() };

        let mk_pending_res = self.make_pending(op, tid, tracked(context_ghost));
        let context_ghost = mk_pending_res.1;

        // Step 2: Try to do flat combining to appy the update to the data structure
        // self.try_combine(slog)?;
        self.try_combine(slog);

        // Step 3: Obtain the result form the responses

        // Return the response to the caller function.
        let response = self.get_response(slog, tid, ghost(req_id), context_ghost);
        let context_ghost = response.1;

        let tracked FCClientRequestResponseGhost { batch_perms, local_updates, fc_clients } = context_ghost.get();
        let tracked local_updates = local_updates.tracked_unwrap();
        let tracked batch_perms = batch_perms.tracked_unwrap();

        // finish the update transaction, return the result

        // TODO: we should obtain this here!
        assert(local_updates@.instance == self.unbounded_log_instance@);
        self.unbounded_log_instance.borrow().update_finish(req_id, local_updates);

        assert(batch_perms@.value.is_None());

        Ok((
            response.0,
            ThreadToken { rid, tid, fc_client: tracked(fc_clients), batch_perm: tracked(batch_perms) }
        ))
    }

    /// Enqueues an operation inside a thread local context. Returns a boolean
    /// indicating whether the operation was enqueued (true) or not (false).
    fn make_pending(&self, op: UpdateOp, tid: ThreadId, context_ghost: Tracked<FCClientRequestResponseGhost>)
     -> (res: (bool, Tracked<FCClientRequestResponseGhost>))
        requires
            self.wf(),
            0 <= tid < self.contexts.len(),
            context_ghost@.enqueue_op_pre(tid as nat, op, self.contexts.spec_index(tid as int).batch.0.id(), self.flat_combiner_instance@, self.unbounded_log_instance@)
        ensures
            res.1@.enqueue_op_post(context_ghost@)
    {
        let context = self.contexts.index(tid as usize);
        context.enqueue_op(op, context_ghost)
    }

    /// Busy waits until a response is available within the thread's context.
    fn get_response(&self, slog: &NrLog, tid: ThreadId, req_id: Ghost<ReqId>, context_ghost: Tracked<FCClientRequestResponseGhost>)
        -> (res: (ReturnType, Tracked<FCClientRequestResponseGhost>))
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            0 <= tid < self.contexts.len(),
            context_ghost@.dequeue_resp_pre(tid as nat, self.flat_combiner_instance@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, Some(res.0), self.unbounded_log_instance@),
    {
        let mut context_ghost_new = context_ghost;
        let context = self.contexts.index(tid as usize);

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
                r.is_None() ==> context_ghost_new@.dequeue_resp_pre(tid as nat, self.flat_combiner_instance@),
                context_ghost_new@.dequeue_resp_post(context_ghost@, r, self.unbounded_log_instance@)
        {
            if iter == RESPONSE_CHECK_INTERVAL {
                self.try_combine(slog);
                iter = 0;
            }

            let deq_resp_result = context.dequeue_response(context_ghost_new);
            assert(deq_resp_result.1@.dequeue_resp_post(context_ghost@, deq_resp_result.0, self.unbounded_log_instance@));
            r = deq_resp_result.0;
            context_ghost_new = deq_resp_result.1;

            iter = iter + 1;
        }

        let r = r.unwrap();
        (r, context_ghost_new)
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
    // replicas: Vec<Box<Replica<DataStructureType, UpdateOp, ReturnType>>>,
    pub (crate) replicas: Vec<Box<Replica>>,

    /// XXX: should that be here, or go into the NrLog / replicas?
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance>,
}



/// Proof blocks for the NodeReplicate data structure
impl NodeReplicated {
    /// Wellformedness of the NodeReplicated data structure
    pub open spec fn wf(&self) -> bool {
        // the log shall be well-formed and the instances match
        &&& self.log.wf()
        &&& self.unbounded_log_instance@ == self.log.unbounded_log_instance@
        &&& self.cyclic_buffer_instance@ == self.log.cyclic_buffer_instance@

        // the number of replicas should be the as configured
        &&& self.replicas.spec_len() == NUM_REPLICAS

        // the replicas should be well-formed and the instances match
        &&& (forall |i| 0 <= i < self.replicas.len() ==> {
            &&& (#[trigger] self.replicas[i]).wf()
            &&& self.replicas[i].spec_id() == i
            &&& self.replicas[i].unbounded_log_instance@ == self.unbounded_log_instance@
            &&& self.replicas[i].cyclic_buffer_instance@ == self.cyclic_buffer_instance@
        })
    }
}


impl NodeReplicated {
    /// Creates a new, replicated data-structure from a single-threaded
    /// data-structure that implements [`Dispatch`]. It uses the [`Default`]
    /// constructor to create a initial data-structure for `D` on all replicas.
    ///
    ///  - Dafny: n/a ?
    ///  - Rust:  pub fn new(num_replicas: NonZeroUsize) -> Result<Self, NodeReplicatedError>
    // pub fn init(num_replicas: usize) -> (res: Self)
    //     requires num_replicas > 0
    //     ensures res.wf()
    // {
    //     arbitrary()
    // //     NodeReplicated {
    // //         log: NrLog::new(),
    // //         replicas: Vec::new(),
    // //     }
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
    pub fn execute_mut(&self, op: UpdateOp, tkn: ThreadToken) -> Result<(ReturnType, ThreadToken), ThreadToken>
        requires
            self.wf() && tkn.wf(),
            tkn.fc_client@@.instance == self.replicas.spec_index(tkn.replica_id_spec() as int).flat_combiner_instance,
            tkn.batch_perm@@.pcell == self.replicas.spec_index(tkn.replica_id_spec() as int).contexts.spec_index(tkn.tid as int).batch.0.id(),
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            self.replicas.index(replica_id).execute_mut(&self.log, op, tkn)
        } else {
            Err(tkn)
        }
    }


    /// Executes a immutable operation against the data-structure.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn execute(&self, op: <D as Dispatch>::ReadOperation<'_>, tkn: ThreadToken,)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    pub fn execute(&self, op: ReadonlyOp, tkn: ThreadToken) -> Result<(ReturnType, ThreadToken), ThreadToken>
        requires
            self.wf() && tkn.wf(),
            tkn.fc_client@@.instance == self.replicas.spec_index(tkn.replica_id_spec() as int).flat_combiner_instance,
            tkn.batch_perm@@.pcell == self.replicas.spec_index(tkn.replica_id_spec() as int).contexts.spec_index(tkn.tid as int).batch.0.id(),
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id< self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            self.replicas.index(replica_id).execute(&self.log, op, tkn)
        } else {
            Err(tkn)
        }
    }
}




////////////////////////////////////////////////////////////////////////////////////////////////////
// RwLockWriteGuard
////////////////////////////////////////////////////////////////////////////////////////////////////

/// structure used to release the exclusive write access of a lock when dropped.
//
/// This structure is created by the write and try_write methods on RwLockSpec.
tracked struct RwLockWriteGuard<T> {
    handle: Tracked<RwLockSpec::writer<PermissionOpt<T>>>,
    perm: Tracked<PermissionOpt<T>>,
    //foo: Tracked<T>,
    // rw_lock : Ghost<DistRwLock::Instance<T>>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//  RwLockReadGuard
////////////////////////////////////////////////////////////////////////////////////////////////////

/// RAII structure used to release the shared read access of a lock when dropped.
///
/// This structure is created by the read and try_read methods on RwLockSpec.
tracked struct RwLockReadGuard<T> {
    handle: Tracked<RwLockSpec::reader<PermissionOpt<T>>>,
    // rw_lock : Ghost<DistRwLock::Instance<T>>,
}

impl<T> RwLockReadGuard<T> {
    spec fn view(&self) -> T {
        self.handle@@.key.view().value.get_Some_0()
        //self.handle@@.key.get_Some_0()

    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// RwLockSpec
////////////////////////////////////////////////////////////////////////////////////////////////////


struct_with_invariants!{
/// A reader-writer lock
pub struct RwLock<#[verifier(maybe_negative)] T> {
    /// cell containing the data
    cell: PCell<T>,
    /// exclusive access
    exc: CachePadded<AtomicBool<_, RwLockSpec::flag_exc<PermissionOpt<T>>, _>>,
    /// reference count
    rc: CachePadded<AtomicU64<_, RwLockSpec::flag_rc<PermissionOpt<T>>, _>>,

    /// the state machien instance
    tracked inst: RwLockSpec::Instance<PermissionOpt<T>>,
    ghost user_inv: Set<T>,
}

pub closed spec fn wf(&self) -> bool {
    predicate {
        forall |v: PermissionOpt<T>| #[trigger] self.inst.user_inv().contains(v) == (
            equal(v@.pcell, self.cell.id()) && v@.value.is_Some()
                && self.user_inv.contains(v@.value.get_Some_0())
        )
    }

    invariant on exc with (inst) specifically (self.exc.0) is (v: bool, g: RwLockSpec::flag_exc<PermissionOpt<T>>) {
        // g@ === RwLockSpec::token! [ inst => exc ==> v ]
        g@.instance == inst && g@.value == v
    }

    invariant on rc with (inst) specifically (self.rc.0) is (v: u64, g: RwLockSpec::flag_rc<PermissionOpt<T>>) {
        // g@ === RwLockSpec::token! [ inst => rc ==> v ]
        g@.instance == inst && g@.value == v as nat
    }
}
} // struct_with_invariants!


impl<T> RwLock<T> {
    /// Invariant on the data
    pub closed spec fn inv(&self, t: T) -> bool {
        self.user_inv.contains(t)
    }

    spec fn wf_write_handle(&self, write_handle: &RwLockWriteGuard<T>) -> bool {
        &&& write_handle.handle@@.instance == self.inst

        &&& write_handle.perm@@.pcell == self.cell.id()
        &&& write_handle.perm@@.value.is_None()
    }

    spec fn wf_read_handle(&self, read_handle: &RwLockReadGuard<T>) -> bool {
        &&& read_handle.handle@@.instance == self.inst

        &&& read_handle.handle@@.key.view().value.is_Some()
        &&& read_handle.handle@@.key.view().pcell == self.cell.id()
        &&& read_handle.handle@@.count == 1
    }

    fn new(t: T, inv: Ghost<FnSpec(T) -> bool>) -> (res: Self)
        requires
            inv@(t)
        ensures
            res.wf(),
            forall |v: T| res.inv(v) == inv@(v)
    {
        let (cell, perm) = PCell::<T>::new(t);

        let ghost set_inv = Set::new(inv@);

        let ghost user_inv = Set::new(closure_to_fn_spec(|s: PermissionOpt<T>| {
            &&& equal(s@.pcell, cell.id())
            &&& s@.value.is_Some()
            &&& set_inv.contains(s@.value.get_Some_0())
        }));

        let tracked inst;
        let tracked flag_exc;
        let tracked flag_rc;
        proof {
            let tracked (Trk(_inst), Trk(_flag_exc), Trk(_flag_rc), _, _, _, _) =
                RwLockSpec::Instance::<PermissionOpt<T>>::initialize_full(user_inv, perm@, Option::Some(perm.get()));
            inst = _inst;
            flag_exc = _flag_exc;
            flag_rc = _flag_rc;
        }

        let exc = AtomicBool::new(inst, false, flag_exc);
        let rc = AtomicU64::new(inst, 0, flag_rc);

        RwLock { cell, exc: CachePadded(exc), rc: CachePadded(rc), inst, user_inv: set_inv }
    }

    fn acquire_write(&self) -> (res: (T, Tracked<RwLockWriteGuard<T>>))
        requires self.wf()
        ensures self.wf_write_handle(&res.1@) && self.inv(res.0)
    {

        let mut done = false;
        let tracked mut token: Option<RwLockSpec::pending_writer<PermissionOpt<T>>> = Option::None;
        while !done
            invariant
                self.wf(),
                done ==> token.is_Some() && token.get_Some_0()@.instance == self.inst,
        {
            let result = atomic_with_ghost!(
                &self.exc.0 => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res.is_Ok() {
                    token = Option::Some(self.inst.acquire_exc_start(&mut g));
                }
            });

            done = match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }

        loop
            invariant
                self.wf(),
                token.is_Some() && token.get_Some_0()@.instance == self.inst,
        {

            let tracked mut perm_opt: Option<PermissionOpt<T>> = Option::None;
            let tracked mut handle_opt: Option<RwLockSpec::writer<PermissionOpt<T>>> =Option::None;
            let tracked acquire_exc_end_result; // need to define tracked, can't in the body
            let result = atomic_with_ghost!(
                &self.rc.0 => load();
                returning res;
                ghost g => {
                if res == 0 {
                    acquire_exc_end_result = self.inst.acquire_exc_end(&g, token.tracked_unwrap());
                    token = Option::None;
                    perm_opt = Option::Some(acquire_exc_end_result.1.0);
                    handle_opt = Option::Some(acquire_exc_end_result.2.0);
                }
            });

            if result == 0 {
                let mut perm = tracked(perm_opt.tracked_unwrap());
                let tracked handle = tracked(handle_opt.tracked_unwrap());

                let t = self.cell.take(&mut perm);

                let tracked write_handle = RwLockWriteGuard { perm, handle };
                return (t, tracked(write_handle));
            }
        }
    }

    fn acquire_read(&self) -> (res: Tracked<RwLockReadGuard<T>>)
        requires self.wf()
        ensures
            self.wf_read_handle(&res@) && self.inv(res@@)
    {
        loop
            invariant self.wf()
        {

            let val = atomic_with_ghost!(&self.rc.0 => load(); ghost g => { });

            let tracked mut token: Option<RwLockSpec::pending_reader<PermissionOpt<T>>> = Option::None;

            if val < 18446744073709551615 {
                let result = atomic_with_ghost!(
                    &self.rc.0 => compare_exchange(val, val + 1);
                    returning res;
                    ghost g =>
                {
                    if res.is_Ok() {
                        token = Option::Some(self.inst.acquire_read_start(&mut g));
                    }
                });

                match result {
                    Result::Ok(_) => {
                        let tracked mut handle_opt: Option<RwLockSpec::reader<PermissionOpt<T>>> = Option::None;
                        let tracked acquire_read_end_result;
                        let result = atomic_with_ghost!(
                            &self.exc.0 => load();
                            returning res;
                            ghost g =>
                        {
                            if res == false {
                                acquire_read_end_result = self.inst.acquire_read_end(&g, token.tracked_unwrap());
                                token = Option::None;
                                handle_opt = Option::Some(acquire_read_end_result.1.0);
                            }
                        });

                        if result == false {
                            let tracked handle = tracked(handle_opt.tracked_unwrap());
                            return tracked(RwLockReadGuard { handle });
                        } else {
                            let _ = atomic_with_ghost!(
                                &self.rc.0 => fetch_sub(1);
                                ghost g =>
                            {
                                self.inst.acquire_read_abandon(&mut g, token.tracked_unwrap());
                            });
                        }
                    }
                    _ => { }
                }
            }
        }
    }

    fn borrow<'a>(&'a self, read_handle: &'a Tracked<RwLockReadGuard<T>>) -> (res: &'a T)
        requires self.wf() && self.wf_read_handle(&read_handle@)
        ensures res == read_handle@@
    {
        let tracked perm = self.inst.read_guard(read_handle@.handle@@.key, read_handle.borrow().handle.borrow());
        self.cell.borrow(tracked_exec_borrow(perm))
    }

    fn release_write(&self, t: T, write_handle: Tracked<RwLockWriteGuard<T>>)
        requires
            self.wf() && self.wf_write_handle(&write_handle@) && self.inv(t)
    {
        let tracked write_handle = write_handle.get();
        let mut perm = tracked_exec(write_handle.perm.get());

        self.cell.put(&mut perm, t);

        atomic_with_ghost!(
            &self.exc.0 => store(false);
            ghost g =>
        {
            self.inst.release_exc(perm.view(), &mut g, perm.get(), write_handle.handle.get());
        });
    }

    fn release_read(&self, read_handle: Tracked<RwLockReadGuard<T>>)
        requires self.wf() && self.wf_read_handle(&read_handle@)
    {
        let tracked  RwLockReadGuard { handle } = read_handle.get();

        let _ = atomic_with_ghost!(
            &self.rc.0 => fetch_sub(1);
            ghost g =>
        {
            self.inst.release_shared(handle.view().view().key, &mut g, handle.get());
        });
    }

    proof fn lemma_readers_match(tracked &self, tracked read_handle1: &Tracked<RwLockReadGuard<T>>, tracked read_handle2: &Tracked<RwLockReadGuard<T>>)
        requires
            self.wf() && self.wf_read_handle(&read_handle1@) && self.wf_read_handle(&read_handle2@)
        ensures
            read_handle1@@ == read_handle2@@
    {
        self.inst.read_match(
            read_handle1@.handle@@.key,
            read_handle2@.handle@@.key,
            read_handle1.borrow().handle.borrow(),
            read_handle2.borrow().handle.borrow());
    }
}


} // verus!

pub fn main() {}
