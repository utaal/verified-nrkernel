#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{
    prelude::*,
    map::Map,
    vec::Vec,
    cell::{PCell},
    atomic_ghost::{AtomicU64, AtomicBool},
    atomic_with_ghost,
};

use crate::spec::types::{
    NodeId, ReqId, LogIdx, ConcreteLogEntry,

    DataStructureSpec, DataStructureType,
    UpdateOp,ReturnType
};
use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::cyclicbuffer::{CyclicBuffer, StoredType, stored_type_inv, LogicalLogIdx, log_entry_idx, log_entry_alive_value};

use crate::constants::{MAX_REQUESTS, NUM_REPLICAS, MAX_IDX, GC_FROM_HEAD, WARN_THRESHOLD, LOG_SIZE};
// use crate::exec::utils::{print_starvation_warning, panic_with_tail_too_big};
use crate::exec::replica::{ReplicaToken, ReplicaId};
use crate::exec::CachePadded;


verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Utils
////////////////////////////////////////////////////////////////////////////////////////////////////

#[verifier(external_body)] /* vattr */
pub fn print_starvation_warning(line: u32) {
    println!("WARNING({line}): has been looping for `WARN_THRESHOLD` iterations. Are we starving?");
}

#[verifier(external_body)] /* vattr */
pub fn panic_with_tail_too_big() {
    panic!("WARNING: Tail value exceeds the maximum value of u64.");
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Log Entries
////////////////////////////////////////////////////////////////////////////////////////////////////


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
        &&& g@.instance == cyclic_buffer_instance@
        &&& g@.key == cyclic_buffer_idx@
        &&& g@.value === v
    }
}
} // struct_with_invariants

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


////////////////////////////////////////////////////////////////////////////////////////////////////
// NR Log
////////////////////////////////////////////////////////////////////////////////////////////////////


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
    pub/*REVIEW: (crate)*/ local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions, CyclicBuffer::local_versions), _>>>,  // NodeInfo is padded

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
        &&& g@.instance == unbounded_log_instance@
        &&& g@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head) {
        // && (forall v, g :: atomic_inv(head.inner, v, g) <==> g == CBHead(v as int, cb_loc_s))
        &&& g@.instance == cyclic_buffer_instance@
        &&& g@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail, CyclicBuffer::tail)) {
        // && (forall v, g :: atomic_inv(globalTail.inner, v, g) <==> GlobalTailInv(v, g, cb_loc_s))
        &&& g.0@.instance == unbounded_log_instance@
        &&& g.0@.value == v
        &&& g.1@.instance == cyclic_buffer_instance@
        &&& g.1@.value == v
        &&& 0 <= v <= MAX_IDX
    }


    // && (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId, cb_loc_s))
    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_versions)) {


        &&& g.0@.instance == unbounded_log_instance@
        &&& g.0@.key == i
        &&& g.0@.value == v
        &&& g.1@.instance == cyclic_buffer_instance@
        &&& g.1@.key == i
        &&& g.1@.value == v
        &&& 0 <= v <= MAX_IDX
    }
}
} // struct_with_invariants!{



impl NrLog
{
    /// initializes the NrLOg
    pub fn new(num_replicas: usize, log_size: usize) -> (res: (Self, Vec<ReplicaToken>, Tracked<NrLogTokens>))
        requires
            log_size == LOG_SIZE,
            num_replicas == NUM_REPLICAS
        ensures
            res.0.wf(),
            res.0.unbounded_log_instance@ == res.2@.unbounded_log_instance,
            res.0.cyclic_buffer_instance@ == res.2@.cyclic_buffer_instance,
            res.1.len() == num_replicas,
            forall |i| #![trigger res.1[i]] 0 <= i < num_replicas ==> res.1[i].id_spec() == i,
            res.2@.wf(num_replicas as nat)
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
                Tracked(unbounded_log_instance0), // Tracked<Instance>,
                Tracked(ul_log0), //Tracked<Map<LogIdx,log>>,
                Tracked(ul_tail0), //Tracked<tail>,
                Tracked(ul_replicas0), //Tracked<Map<NodeId,replicas>>,
                Tracked(ul_local_versions0), //Tracked<Map<NodeId,local_versions>>,
                Tracked(ul_version_upper_bound0), //Tracked<version_upper_bound>,
                _, //Tracked(ul_local_reads0), //Tracked<Map<ReqId,local_reads>>,
                _, //Tracked(ul_local_updates0), //Tracked<Map<ReqId,local_updates>>,
                Tracked(ul_combiner0), //Tracked<Map<NodeId,combiner>>
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
            proof {
                contents.tracked_insert(logical_log_idx, stored_type);
            }

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
        let tracked cb_combiners            : Map<NodeId, CyclicBuffer::combiner>;

        proof {
            assert(log_size == LOG_SIZE);
            // assert(LOG_SIZE == spec::cyclicbuffer::LOG_SIZE);
            let tracked (
                Tracked(cyclic_buffer_instance0), // CyclicBuffer::Instance>;
                Tracked(cb_head0), // CyclicBuffer::head>;
                Tracked(cb_tail0), // CyclicBuffer::tail>;
                Tracked(cb_local_versions0), // Map<NodeId, CyclicBuffer::local_versions>;
                Tracked(cb_alive_bits0), // Map<LogIdx, CyclicBuffer::alive_bits>;
                Tracked(cb_combiner0), // Map<NodeId, CyclicBuffer::combiner>;
            ) = CyclicBuffer::Instance::initialize(unbounded_log_instance, log_size as nat, num_replicas as nat, contents, contents);
            cyclic_buffer_instance = cyclic_buffer_instance0;
            cb_head = cb_head0;
            cb_tail = cb_tail0;
            cb_local_versions = cb_local_versions0;
            cb_alive_bits = cb_alive_bits0;
            cb_combiners = cb_combiner0;
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

            let tracked cb_inst = Tracked(cyclic_buffer_instance.clone());

            let entry = BufferEntry {
                log_entry: log_entry,
                alive: AtomicBool::new(Ghost((Ghost(log_idx as nat), cb_inst)), false, Tracked(cb_alive_bit)),
                cyclic_buffer_idx: Ghost(log_idx as nat),
                cyclic_buffer_instance: Tracked(cyclic_buffer_instance.clone())
            };
            slog.push(entry);

            log_idx = log_idx + 1;
        }

        let tracked ul_inst = Tracked(unbounded_log_instance.clone());
        let version_upper_bound = CachePadded(AtomicU64::new(Ghost(ul_inst), 0, Tracked(ul_version_upper_bound)));

        let tracked cb_inst = Tracked(cyclic_buffer_instance.clone());
        let head = CachePadded(AtomicU64::new(Ghost(cb_inst), 0, Tracked(cb_head)));

        let tracked cb_inst = Tracked(cyclic_buffer_instance.clone());
        let tracked ul_inst = Tracked(unbounded_log_instance.clone());
        let tail = CachePadded(AtomicU64::new(Ghost((cb_inst, ul_inst)), 0, Tracked((ul_tail, cb_tail))));
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

            let tracked cb_inst = Tracked(cyclic_buffer_instance.clone());
            let tracked ul_inst = Tracked(unbounded_log_instance.clone());

            local_versions.push(CachePadded(AtomicU64::new(Ghost((ul_inst, cb_inst, nid_ghost)), 0, Tracked((ul_version, cb_version)))));

            nid = nid + 1;
        }

        //
        // Create the replica tokens
        //

        let mut replica_tokens : Vec<ReplicaToken> = Vec::with_capacity(num_replicas);
        let mut idx = 0;
        while idx < num_replicas
            invariant
                0 <= idx <= num_replicas,
                num_replicas <= NUM_REPLICAS,
                replica_tokens.len() == idx,
                forall |i| #![trigger replica_tokens[i]] 0 <= i < idx ==> replica_tokens[i].id_spec() == i,
        {
            replica_tokens.push(ReplicaToken::new(idx as ReplicaId));
            idx = idx + 1;
        }

        let ghost mut num_replicas_ghost; proof { num_replicas_ghost = num_replicas as nat };

        let tracked config = NrLogTokens {
            num_replicas: num_replicas_ghost,
            replicas: ul_replicas,
            combiners: ul_combiner,
            cb_combiners,
            unbounded_log_instance: unbounded_log_instance.clone(),
            cyclic_buffer_instance: cyclic_buffer_instance.clone(),
        };

        let log = NrLog {
            slog,
            version_upper_bound,
            head,
            tail,
            local_versions,
            num_replicas : Ghost(num_replicas as nat),
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
        };


        (log, replica_tokens, Tracked(config))
    }


    /// Returns a physical index given a logical index into the shared log.
    #[inline(always)]
    pub(crate) fn index(&self, logical: u64) -> (result: usize)
        requires
            self.slog.len() == LOG_SIZE
        ensures
            result as nat == self.index_spec(logical as nat),
            result == log_entry_idx(logical as int, self.slog.spec_len() as nat),
            result < self.slog.len()
    {
        (logical as usize) % self.slog.len()
    }

    pub/*REVIEW: (crate)*/ open spec fn index_spec(&self, logical: nat) -> nat
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
            result == log_entry_alive_value(logical as int, self.slog.spec_len() as nat)
    {
        ((logical as usize) / LOG_SIZE % 2) == 0
    }

    pub/*REVIEW: (crate)*/ open spec fn is_alive_value_spec(&self, logical: int) -> bool
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

        (res, Tracked(new_local_reads_g))
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
        let rid_g : Ghost<ReqId> = Ghost(local_reads@@.key);
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

        (res >= version_upper_bound, Tracked(new_local_reads_g))
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

        let tracked combiner = update_result.2.get();
        log_entries.tracked_insert(ridx, update_result.0.get());
        local_updates.tracked_insert(ridx, update_result.1.get());

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
        // responses and actual replica are part of the closure
        responses: &mut Vec<ReturnType>,
        actual_replica: &mut DataStructureType,
        // here we also need to pass the mut replica
        ghost_data: Tracked<NrLogAppendExecDataGhost>
    ) -> (result: Tracked<NrLogAppendExecDataGhost>)
        requires
            self.wf(),
            replica_token@ < self.local_versions.len(),
            ghost_data@.append_pre(operations@, replica_token@, self.unbounded_log_instance@, self.cyclic_buffer_instance@),
            operations.len() <= MAX_REQUESTS
        ensures
            result@.append_post(replica_token@,  self.unbounded_log_instance@, self.cyclic_buffer_instance@, operations@, responses@)
    {
        let tracked Tracked(mut ghost_data) = ghost_data;

        let nid = replica_token.id() as usize;

        // // TODO!
        let nops = operations.len();

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
            let tracked NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids} = ghost_data;
            let tracked Tracked(mut cb_combiner) = cb_combiner;
            let tracked Tracked(mut combiner) = combiner;
            let tracked Tracked(local_updates) = local_updates;

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
                    // assert(g.view().instance == self.cyclic_buffer_instance.view());
                    // assert(cb_combiner.view().instance == self.cyclic_buffer_instance.view());
                    // assert(cb_combiner.view().key == nid);
                    // assert(cb_combiner.view().value.is_Idle());
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
            if tail > head + (self.slog.len() as u64 - GC_FROM_HEAD as u64) {
                if waitgc == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    waitgc = 0;
                    // TODO: Return?
                }

                waitgc = waitgc + 1;

                proof {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_tail_abort(nid as nat, cb_combiner);
                }

                let tracked ghost_data0 = NrLogAppendExecDataGhost { local_updates: Tracked(local_updates), ghost_replica, combiner: Tracked(combiner), cb_combiner: Tracked(cb_combiner), request_ids};
                let ghost_data0 = self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
                let ghost_data0 = self.advance_head(replica_token, responses, actual_replica, ghost_data0);
                let tracked Tracked(ghost_data0) = ghost_data0;
                proof {
                    ghost_data = ghost_data0;
                }
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

                let tracked ghost_data0 = NrLogAppendExecDataGhost { local_updates: Tracked(Map::tracked_empty()), ghost_replica, combiner: Tracked(combiner), cb_combiner: Tracked(cb_combiner), request_ids: Ghost(Seq::empty())};
                return Tracked(ghost_data0);
            }

            // If on adding in the above entries there would be fewer than `GC_FROM_HEAD`
            // entries left on the log, then we need to advance the head of the log.
            let advance = new_tail > head + (self.slog.len() - GC_FROM_HEAD) as u64 ;

            // Try reserving slots for the operations. If that fails, then restart
            // from the beginning of this loop.
            // if self.tail.compare_exchange_weak(tail, tail + nops, Ordering::Acquire, Ordering::Acquire) !+ Ok(tail) {
            //     continue;
            // }

            let tracked advance_tail_finish_result : (Ghost<Map<LogicalLogIdx,StoredType>>, Tracked<Map<LogicalLogIdx, StoredType>>, Tracked<CyclicBuffer::combiner>);
            let tracked mut append_entries_ghost_state : AppendEntriesGhostState;
            let tracked mut cb_log_entries : Map<int, StoredType> = Map::tracked_empty();
            let tracked mut log_entries : Map<nat,UnboundedLog::log> = Map::tracked_empty();

            // seems required to get the contains properly
            assert(forall |i| 0 <= i < request_ids@.len() ==> local_updates.contains_key(i));

            // let tracked local_update ;// UnboundedLog::local_updates
            let result = atomic_with_ghost!(
                //&self.tail.0 => compare_exchange(tail, new_tail);
                &self.tail.0 => compare_exchange_weak(tail, new_tail);
                update prev -> next;
                returning result;
                ghost g => {
                    if matches!(result, Result::Ok(tail)) {
                        let tracked (mut unbounded_tail, mut cb_tail) = g;

                        assert(tail <= new_tail);
                        assert(new_tail <= head + self.slog.len());

                        advance_tail_finish_result = self.cyclic_buffer_instance.borrow()
                            .advance_tail_finish(nid as nat, new_tail as nat, &mut cb_tail, cb_combiner);

                        cb_combiner = advance_tail_finish_result.2.get();
                        cb_log_entries = advance_tail_finish_result.1.get();

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
                proof {
                    ghost_data = NrLogAppendExecDataGhost {
                        local_updates: Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                        ghost_replica,  // Tracked<UnboundedLog::replicas>,
                        combiner: Tracked(combiner),       // Tracked<UnboundedLog::combiner>,
                        cb_combiner: Tracked(cb_combiner),    // Tracked<CyclicBuffer::combiner>,
                        request_ids,    // Ghost<Seq<ReqId>>,
                    };
                }
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
                let tracked mut cb_log_entry_perms = cb_log_entry.cell_perms;

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
                assert(cb_log_entry_perms@.pcell == self.slog.spec_index(log_idx as int).log_entry.id());

                // update the log entry in the buffer
                self.slog.index(log_idx).log_entry.replace(Tracked(&mut cb_log_entry_perms), new_log_entry);

                assert(cb_log_entry_perms@.value.is_Some());
                assert(cb_log_entry_perms@.value.get_Some_0().node_id == nid as u64);
                assert(cb_log_entry_perms@.value.get_Some_0().op == operations.spec_index(idx as int));

                // unsafe { (*e).alivef.store(m, Ordering::Release) };
                let m = self.is_alive_value(logical_log_idx as u64);

                let tracked append_flip_bit_result;
                let tracked new_stored_type;

                atomic_with_ghost!(
                    &self.slog.index(log_idx).alive => store(m);
                    ghost g => {
                        new_stored_type = StoredType {
                            cell_perms: cb_log_entry_perms,
                            log_entry: Option::Some(log_entries.tracked_remove(idx as nat)),
                        };

                        let c_cur_idx = cb_combiner.view().value.get_Appending_cur_idx();

                        assert(stored_type_inv(new_stored_type, c_cur_idx as int, self.unbounded_log_instance.view()));

                        append_flip_bit_result = self.cyclic_buffer_instance.borrow()
                            .append_flip_bit(nid as NodeId, new_stored_type, new_stored_type, g, cb_combiner);
                        g = append_flip_bit_result.0.get();
                        cb_combiner = append_flip_bit_result.1.get();
                    }
                );

                idx = idx + 1;
            }

            proof {
                cb_combiner = self.cyclic_buffer_instance.borrow().append_finish(nid as nat, cb_combiner);
            }

            proof {
                ghost_data = NrLogAppendExecDataGhost {
                    local_updates:Tracked(local_updates),   // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                    ghost_replica,                          // Tracked<UnboundedLog::replicas>,
                    combiner: Tracked(combiner),            // Tracked<UnboundedLog::combiner>,
                    cb_combiner: Tracked(cb_combiner),      // Tracked<CyclicBuffer::combiner>,
                    request_ids,                            // Ghost<Seq<ReqId>>,
                };
            }

            return if advance {
                self.advance_head(replica_token, responses, actual_replica, Tracked(ghost_data))
            } else {
                Tracked(ghost_data)
            }
        }

    }


    /// Advances the head of the log forward. If a replica has stopped making
    /// progress, then this method will never return. Accepts a closure that is
    /// passed into execute() to ensure that this replica does not deadlock GC.
    fn advance_head(&self, replica_token: &ReplicaToken,
                    // the following were part of the closure
                    responses: &mut Vec<ReturnType>,
                    actual_replica: &mut DataStructureType,
                    // ghost state for execute etc.
                    ghost_data: Tracked<NrLogAppendExecDataGhost>)
            -> (res: Tracked<NrLogAppendExecDataGhost>)
        requires
            self.wf(),
            ghost_data@.execute_pre(replica_token.id_spec(), self.unbounded_log_instance@, self.cyclic_buffer_instance@),
        ensures
            res@.execute_pre(replica_token.id_spec(), self.unbounded_log_instance@, self.cyclic_buffer_instance@),
    {
        let mut ghost_data = ghost_data;

        let mut iteration = 1;
        loop
            invariant
                self.wf(),
                ghost_data@.execute_pre(replica_token.id_spec(), self.unbounded_log_instance@, self.cyclic_buffer_instance@),
                0 <= iteration <= WARN_THRESHOLD
        {
            let Tracked(ghost_data0) = ghost_data;
            let tracked NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids } = ghost_data0;
            let tracked Tracked(mut cb_combiner) = cb_combiner;

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

            let (min_local_version, cb_combiner0) = self.find_min_local_version(Tracked(cb_combiner));
            let tracked Tracked(mut cb_combiner) = cb_combiner0;
            // let res = ;
            // let min_local_version = res.0;
            // proof {
            //     g_cb_comb_new = res.1.get();
            // }

            // If we cannot advance the head further, then start
            // from the beginning of this loop again. Before doing so, try consuming
            // any new entries on the log to prevent deadlock.
            if min_local_version == global_head {
                proof {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_head_abort(replica_token.id_spec(), cb_combiner);
                }
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    // let tracked cb_combiner = Tracked(cb_combiner);
                    // let tracked ghost_data = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
                    // return Tracked(ghost_data);
                }
                iteration = iteration + 1;
            } else {
                // There are entries that can be freed up; update the head offset.
                // self.head.store(min_local_tail, Ordering::Relaxed);
                atomic_with_ghost!(
                    &self.head.0 => store(min_local_version);
                    update old_val -> new_val;
                    ghost g => {
                        cb_combiner = self.cyclic_buffer_instance.borrow().advance_head_finish(replica_token.id_spec(), &mut g, cb_combiner);
                });

                if global_tail < min_local_version + self.slog.len() as u64 - GC_FROM_HEAD as u64 {
                    let tracked cb_combiner = Tracked(cb_combiner);
                    let tracked ghost_data = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
                    return Tracked(ghost_data);
                }
            }

            let tracked cb_combiner = Tracked(cb_combiner);
            let tracked ghost_data0 = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
            ghost_data = self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
        }
    }

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
            let tracked combiner = Tracked(combiner);
            let tracked cb_combiner = Tracked(cb_combiner);
            let tracked ghost_replica = Tracked(ghost_replica);
            let tracked local_updates = Tracked(local_updates);
            let tracked request_ids = Ghost(request_ids);
            let tracked ghost_data = NrLogAppendExecDataGhost {
                local_updates,  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                ghost_replica,  // Tracked<UnboundedLog::replicas>,
                combiner,       // Tracked<UnboundedLog::combiner>,
                cb_combiner,    // Tracked<CyclicBuffer::combiner>,
                request_ids,    // Ghost<Seq<ReqId>>,
            };
            let res = Tracked(ghost_data);
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

                let tracked reader_guard_result : (Ghost<Map<int, StoredType>>,Tracked<CyclicBuffer::combiner>);
                let alive_bit = atomic_with_ghost!(
                    &self.slog.index(phys_log_idx).alive => load();
                    returning alive_bit;
                    ghost g => {
                        if alive_bit == is_alive_value {
                            assert(g.view().key == phys_log_idx);
                            reader_guard_result = self.cyclic_buffer_instance.borrow().reader_guard(nid as nat, &g, cb_combiner);
                            cb_combiner = reader_guard_result.1.get();
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
            let log_entry = self.slog.index(phys_log_idx).log_entry.borrow(Tracked(&stored_entry.cell_perms));

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
                        ghost_replica = exec_dispatch_local_result.0.get();

                        assert(exec_dispatch_local_result.1@@.value.is_Applied());
                        assert(exec_dispatch_local_result.1@@.value.get_Applied_ret() == res);

                        local_updates.tracked_insert(responses_idx as nat, exec_dispatch_local_result.1.get());
                        combiner = exec_dispatch_local_result.2.get();


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
                        ghost_replica = exec_dispatch_remote_result.0.get();
                        combiner = exec_dispatch_remote_result.1.get();
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


        let tracked reader_finish_result : (Tracked<CyclicBuffer::local_versions>, Tracked<CyclicBuffer::combiner>);
        let tracked exec_finish_result : (Tracked<UnboundedLog::local_versions>, Tracked<UnboundedLog::combiner>);
        // self.ltails[idx.0 - 1].store(gtail, Ordering::Relaxed);
        atomic_with_ghost!(
            &self.local_versions.index(nid).0 => store(global_tail);
            ghost g => {
                exec_finish_result = self.unbounded_log_instance.borrow().exec_finish(nid as nat, g.0, combiner);
                reader_finish_result = self.cyclic_buffer_instance.borrow().reader_finish(nid as nat, g.1, cb_combiner);

                combiner = exec_finish_result.1.get();
                cb_combiner = reader_finish_result.1.get();

                g = (exec_finish_result.0.get(), reader_finish_result.0.get());
        });

        let tracked combiner = Tracked(combiner);
        let tracked cb_combiner = Tracked(cb_combiner);
        let tracked local_updates = Tracked(local_updates);
        let tracked ghost_replica = Tracked(ghost_replica);
        let tracked request_ids = Ghost(request_ids);
        let tracked ghost_data = NrLogAppendExecDataGhost {
            local_updates,  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
            ghost_replica,  // Tracked<UnboundedLog::replicas>,
            combiner,       // Tracked<UnboundedLog::combiner>,
            cb_combiner,    // Tracked<CyclicBuffer::combiner>,
            request_ids,    // Ghost<Seq<ReqId>>,
        };
        assume(false);
        Tracked(ghost_data)
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
        (min_local_version, Tracked(g_cb_comb_new))
    }


    // pub fn register(&mut self) -> Option<ReplicaToken> {
    //     if self.replica_tokens.len() > 0 {
    //         Option::Some(self.replica_tokens.pop())
    //     } else {
    //         Option::None
    //     }
    // }

}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost State
////////////////////////////////////////////////////////////////////////////////////////////////////



/// Data structure that is passed between the append and exec functins of the log.
pub tracked struct NrLogAppendExecDataGhost {
    pub /* REVIEW (crate) */ local_updates: Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
    pub /* REVIEW (crate) */ ghost_replica: Tracked<UnboundedLog::replicas>,
    pub /* REVIEW (crate) */ combiner: Tracked<UnboundedLog::combiner>,
    pub /* REVIEW (crate) */ cb_combiner: Tracked<CyclicBuffer::combiner>,
    pub /* REVIEW (crate) */ request_ids: Ghost<Seq<ReqId>>,
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
/// represents the tokens that are created when a new log is being initialized
pub tracked struct NrLogTokens {
    pub ghost num_replicas: nat,
    pub tracked replicas    : Map<NodeId,UnboundedLog::replicas>,
    pub tracked combiners   : Map<NodeId,UnboundedLog::combiner>,
    pub tracked cb_combiners: Map<NodeId, CyclicBuffer::combiner>,
    pub tracked unbounded_log_instance: UnboundedLog::Instance,
    pub tracked cyclic_buffer_instance: CyclicBuffer::Instance,
}

pub open spec fn wf(&self, num_replicas: nat) -> bool {
    predicate {
        &&& self.num_replicas == num_replicas
        &&& (forall |i| #![trigger self.replicas[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.replicas.contains_key(i)
            &&& self.replicas[i]@.instance == self.unbounded_log_instance
            &&& self.replicas[i]@.key == i
            &&& self.replicas[i]@.value == DataStructureSpec::init()
        })

        &&& (forall |i| #![trigger self.combiners[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger]  self.combiners.contains_key(i)
            &&& self.combiners[i]@.instance == self.unbounded_log_instance
            &&& self.combiners[i]@.key == i
            &&& self.combiners[i]@.value.is_Ready()
        })

        &&& (forall |i| #![trigger self.cb_combiners[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.cb_combiners.contains_key(i)
            &&& self.cb_combiners[i]@.instance == self.cyclic_buffer_instance
            &&& self.cb_combiners[i]@.key == i
            &&& self.cb_combiners[i]@.value.is_Idle()
        })
    }
}

} // struct_with_invariants!{

} // verus!