#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{
    atomic_ghost::{AtomicBool, AtomicU64},
    atomic_with_ghost,
    cell::{CellId, PCell},
    map::Map,
    prelude::*,
};

#[cfg(verus_keep_ghost)]
use crate::spec::cyclicbuffer::{log_entry_alive_value, log_entry_idx, stored_type_inv};
use crate::spec::cyclicbuffer::{CyclicBuffer, LogicalLogIdx, StoredType};
use crate::spec::types::{ConcreteLogEntry, LogIdx, NodeId, ReqId};
use crate::spec::unbounded_log::UnboundedLog;
use crate::Dispatch;

use crate::constants::{
    GC_FROM_HEAD, LOG_SIZE, MAX_IDX, MAX_REPLICAS, MAX_REQUESTS, WARN_THRESHOLD,
};
use crate::exec::replica::{ReplicaId, ReplicaToken};
use crate::exec::CachePadded;

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Utils
////////////////////////////////////////////////////////////////////////////////////////////////////
#[verus::line_count::ignore]
#[verus::trusted]
#[verifier(external_body)]  /* vattr */
pub fn print_starvation_warning(line: u32) {
    eprintln!("WARNING({line}): has been looping for `WARN_THRESHOLD` iterations. Are we starving?");
}

#[verus::trusted]
#[verifier(external_body)]  /* vattr */
pub fn warn_with_tail_too_big() {
    eprintln!("WARNING: Tail value exceeds the maximum value of u64.");
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
pub struct BufferEntry<DT: Dispatch> {
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
    pub log_entry: PCell<Option<ConcreteLogEntry<DT>>>,

    /// Indicates whether this entry represents a valid operation when on the log.
    ///
    ///  - Dafny: linear alive: Atomic<bool, CBAliveBit>)
    ///  - Rust:  pub(crate) alivef: AtomicBool,
    pub alive: AtomicBool<_, CyclicBuffer::alive_bits<DT>, _>,

    /// the index into the cyclic buffer of this entry into the cyclig buffer.
    pub cyclic_buffer_idx: Ghost<nat>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>
}

pub open spec fn wf(&self, idx: nat, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
    predicate {
        &&& self.cyclic_buffer_instance@ == cb_inst
        &&& self.cyclic_buffer_idx == idx
    }
    invariant on alive with (cyclic_buffer_idx, cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits<DT>) {
        &&& g@.instance == cyclic_buffer_instance@
        &&& g@.key == cyclic_buffer_idx@
        &&& g@.value === v
    }
}
}  // struct_with_invariants
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
pub struct NrLog<DT: Dispatch>
{
    /// The actual log, a slice of entries.
    ///  - Dafny: linear buffer: lseq<BufferEntry>,
    ///           glinear bufferContents: GhostAtomic<CBContents>,
    ///  - Rust:  pub(crate) slog: Box<[Cell<Entry<T, M>>]>,
    pub slog: Vec<BufferEntry<DT>>,

    /// Completed tail maintains an index <= tail that points to a log entry after which there
    /// are no completed operations across all replicas registered against this log.
    ///
    ///  - Dafny: linear ctail: CachePadded<Atomic<uint64, Ctail>>,
    ///  - Rust:  pub(crate) ctail: CachePadded<AtomicUsize>,
    pub version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound<DT>, _>>,

    /// Logical index into the above slice at which the log starts.
    ///
    ///  - Dafny: linear head: CachePadded<Atomic<uint64, CBHead>>,
    ///  - Rust:  pub(crate) head: CachePadded<AtomicUsize>,
    pub head: CachePadded<AtomicU64<_, CyclicBuffer::head<DT>, _>>,

    /// Logical index into the above slice at which the log ends. New appends go here.
    ///
    ///  - Dafny: linear globalTail: CachePadded<Atomic<uint64, GlobalTailTokens>>,
    ///  - Rust:  pub(crate) tail: CachePadded<AtomicUsize>,
    pub tail: CachePadded<AtomicU64<_, (UnboundedLog::tail<DT>, CyclicBuffer::tail<DT>), _>>,

    /// Array consisting of the local tail of each replica registered with the log.
    /// Required for garbage collection; since replicas make progress over the log
    /// independently, we want to make sure that we don't garbage collect operations
    /// that haven't been executed by all replicas.
    ///
    ///  - Dafny: linear node_info: lseq<NodeInfo>, // NodeInfo is padded
    ///  - Rust:  pub(crate) ltails: [CachePadded<AtomicUsize>; MAX_REPLICAS_PER_LOG],
    ///
    pub/*REVIEW: (crate)*/ local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>), _>>>,  // NodeInfo is padded

    // The upstream Rust version also contains:
    //  - pub(crate) next: CachePadded<AtomicUsize>, the identifier for the next replica
    //  - pub(crate) lmasks: [CachePadded<Cell<bool>>; MAX_REPLICAS_PER_LOG], tracking of alivebits

    pub num_replicas: Ghost<nat>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}

pub open spec fn wf(&self) -> bool {
    predicate {
        &&& 0 < self.num_replicas@ <=  MAX_REPLICAS

        &&& self.local_versions.len() == self.num_replicas

        &&& self.slog.len() == LOG_SIZE
        &&& self.slog.len() == self.cyclic_buffer_instance@.buffer_size()
        &&& self.slog.len() == self.cyclic_buffer_instance@.cell_ids().len()
        &&& (forall |i| #![trigger self.slog[i]] 0 <= i < self.slog.len() ==> {
            &&& self.slog[i].log_entry.id() == (#[trigger]self.cyclic_buffer_instance@.cell_ids()[i])
        })

        &&& (forall |i: nat| i < LOG_SIZE ==> (#[trigger] self.slog[i as int]).wf(i, self.cyclic_buffer_instance@))

        &&& self.unbounded_log_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.unbounded_log_instance() == self.unbounded_log_instance
    }

    invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound<DT>) {
        &&& g@.instance == unbounded_log_instance@
        &&& g@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head<DT>) {
        &&& g@.instance == cyclic_buffer_instance@
        &&& g@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail<DT>, CyclicBuffer::tail<DT>)) {
        &&& g.0@.instance == unbounded_log_instance@
        &&& g.0@.value == v
        &&& g.1@.instance == cyclic_buffer_instance@
        &&& g.1@.value == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>)) {

        &&& g.0@.instance == unbounded_log_instance@
        &&& g.0@.key == i
        &&& g.0@.value == v
        &&& g.1@.instance == cyclic_buffer_instance@
        &&& g.1@.key == i
        &&& g.1@.value == v
        &&& 0 <= v <= MAX_IDX
    }
}
}  // struct_with_invariants!{


impl<DT: Dispatch> NrLog<DT> {
    /// initializes the NrLOg
    pub fn new(num_replicas: usize, log_size: usize) -> (res: (
        Self,
        Vec<ReplicaToken>,
        Tracked<NrLogTokens<DT>>,
    ))
        requires
            log_size == LOG_SIZE,
            0 < num_replicas && num_replicas <= MAX_REPLICAS,
        ensures
            res.0.wf(),
            res.0.unbounded_log_instance@ == res.2@.unbounded_log_instance,
            res.0.cyclic_buffer_instance@ == res.2@.cyclic_buffer_instance,
            res.1.len() == num_replicas,
            forall|i| #![trigger res.1[i]] 0 <= i < num_replicas ==> res.1[i].id_spec() == i,
            res.2@.wf(num_replicas as nat),
    {
        //
        // initialize the unbounded log state machine to obtain the tokens
        //
        let tracked unbounded_log_instance: UnboundedLog::Instance<DT>;
        let tracked ul_log: Map<LogIdx, UnboundedLog::log<DT>>;
        let tracked ul_tail: UnboundedLog::tail<DT>;
        let tracked ul_replicas: Map<NodeId, UnboundedLog::replicas<DT>>;
        let tracked mut ul_local_versions: Map<NodeId, UnboundedLog::local_versions<DT>>;
        let tracked ul_version_upper_bound: UnboundedLog::version_upper_bound<DT>;
        let tracked ul_combiner: Map<NodeId, UnboundedLog::combiner<DT>>;
        proof {
            let tracked (
                Tracked(unbounded_log_instance0),  // Tracked<Instance>,
                Tracked(ul_log0),  //Tracked<Map<LogIdx,log>>,
                Tracked(ul_tail0),  //Tracked<tail>,
                Tracked(ul_replicas0),  //Tracked<Map<NodeId,replicas>>,
                Tracked(ul_local_versions0),  //Tracked<Map<NodeId,local_versions>>,
                Tracked(ul_version_upper_bound0),  //Tracked<version_upper_bound>,
                _,  //Tracked(ul_local_reads0), //Tracked<Map<ReqId,local_reads>>,
                _,  //Tracked(ul_local_updates0), //Tracked<Map<ReqId,local_updates>>,
                Tracked(ul_combiner0),  //Tracked<Map<NodeId,combiner>>
            ) = UnboundedLog::Instance::initialize(num_replicas as nat);
            unbounded_log_instance = unbounded_log_instance0;
            ul_log = ul_log0;
            ul_tail = ul_tail0;
            ul_replicas = ul_replicas0;
            ul_local_versions = ul_local_versions0;
            ul_version_upper_bound = ul_version_upper_bound0;
            ul_combiner = ul_combiner0;
        }
        //
        // initialize the log cells
        //
        let ghost mut logical_log_idx;
        proof {
            logical_log_idx = -log_size as int;
        }
        let mut slog_entries: Vec<Option<PCell<Option<ConcreteLogEntry<DT>>>>> = Vec::with_capacity(
            log_size,
        );
        let ghost mut cell_ids: Seq<CellId> = Seq::empty();
        let tracked mut contents: Map<LogicalLogIdx, StoredType<DT>> = Map::tracked_empty();
        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                log_size == LOG_SIZE,
                logical_log_idx == log_idx - log_size,
                -log_size <= logical_log_idx <= 0,
                slog_entries.len() == log_idx,
                cell_ids.len() == log_idx,
                forall|i| 0 <= i < log_idx ==> (#[trigger] slog_entries[i]).is_Some(),
                forall|i|
                    0 <= i < log_idx ==> #[trigger] cell_ids[i] == (
                    #[trigger] slog_entries[i]).get_Some_0().id(),
                forall|i| -log_size <= i < logical_log_idx <==> #[trigger] contents.contains_key(i),
                forall|i| #[trigger]
                    contents.contains_key(i) ==> stored_type_inv(
                        contents[i],
                        i,
                        cell_ids[log_entry_idx(i, log_size as nat) as int],
                        unbounded_log_instance,
                    ),
        {
            // pub log_entry: PCell<ConcreteLogEntry>,
            // create the log entry cell, TODO: create the concrete log entry here?
            let (pcell, token) = PCell::new(Option::None);
            // add the cell to the log entries for later, store the id
            proof {
                cell_ids = cell_ids.push(pcell.id());
            }
            slog_entries.push(Option::Some(pcell));
            // create the stored type
            let tracked stored_type = StoredType {
                cell_perms: token.get(),
                log_entry: Option::None,
            };
            // add the stored type to the contents map
            proof {
                contents.tracked_insert(logical_log_idx, stored_type);
            }
            log_idx = log_idx + 1;
            proof {
                logical_log_idx = logical_log_idx + 1;
            }
        }
        //
        // Create the cyclic buffer state machine
        //

        let tracked cyclic_buffer_instance: CyclicBuffer::Instance<DT>;
        let tracked cb_head: CyclicBuffer::head<DT>;
        let tracked cb_tail: CyclicBuffer::tail<DT>;
        let tracked mut cb_local_versions: Map<NodeId, CyclicBuffer::local_versions<DT>>;
        let tracked mut cb_alive_bits: Map<LogIdx, CyclicBuffer::alive_bits<DT>>;
        let tracked cb_combiners: Map<NodeId, CyclicBuffer::combiner<DT>>;
        proof {
            let tracked (
                Tracked(cyclic_buffer_instance0),  // CyclicBuffer::Instance>;
                Tracked(cb_head0),  // CyclicBuffer::head>;
                Tracked(cb_tail0),  // CyclicBuffer::tail>;
                Tracked(cb_local_versions0),  // Map<NodeId, CyclicBuffer::local_versions>;
                Tracked(cb_alive_bits0),  // Map<LogIdx, CyclicBuffer::alive_bits>;
                Tracked(cb_combiner0),  // Map<NodeId, CyclicBuffer::combiner>;
            ) = CyclicBuffer::Instance::initialize(
                log_size as nat,
                num_replicas as nat,
                contents,
                cell_ids,
                unbounded_log_instance,
                contents,
            );
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
        let mut slog: Vec<BufferEntry<DT>> = Vec::with_capacity(log_size);
        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                slog_entries.len() == log_size,
                slog.len() == log_idx,
                cell_ids.len() == log_size,
                forall|i|
                    #![trigger slog[i]]
                    0 <= i < log_idx ==> {
                        &&& slog[i].wf(i as nat, cyclic_buffer_instance)
                        &&& slog[i].log_entry.id() == (#[trigger] cell_ids[i])
                    },
                forall|i| log_idx <= i < log_size ==> cb_alive_bits.contains_key(i),
                forall|i|
                    #![trigger cb_alive_bits[i]]
                    log_idx <= i < log_size ==> {
                        &&& cb_alive_bits[i]@.key == i
                        &&& cb_alive_bits[i]@.value == false
                        &&& cb_alive_bits[i]@.instance == cyclic_buffer_instance
                    },
                forall|i| 0 <= i < log_idx ==> slog_entries.spec_index(i).is_None(),
                forall|i|
                    #![trigger slog_entries[i]]
                    log_idx <= i < log_size ==> {
                        &&& slog_entries[i].is_Some()
                        &&& slog_entries[i].get_Some_0().id() == cell_ids[i]
                    },
        {
            let tracked cb_alive_bit;
            proof {
                cb_alive_bit = cb_alive_bits.tracked_remove(log_idx as nat);
            }
            let mut log_entry = Option::None;
            slog_entries.set_and_swap(log_idx, &mut log_entry);
            assert(log_entry.is_Some());
            let log_entry = log_entry.unwrap();
            let cb_inst = Tracked(cyclic_buffer_instance.clone());
            let entry = BufferEntry {
                log_entry: log_entry,
                alive: AtomicBool::new(
                    Ghost((Ghost(log_idx as nat), cb_inst)),
                    false,
                    Tracked(cb_alive_bit),
                ),
                cyclic_buffer_idx: Ghost(log_idx as nat),
                cyclic_buffer_instance: Tracked(cyclic_buffer_instance.clone()),
            };
            slog.push(entry);
            log_idx = log_idx + 1;
        }
        let ul_inst = Tracked(unbounded_log_instance.clone());
        let version_upper_bound = CachePadded(
            AtomicU64::new(Ghost(ul_inst), 0, Tracked(ul_version_upper_bound)),
        );
        let cb_inst = Tracked(cyclic_buffer_instance.clone());
        let head = CachePadded(AtomicU64::new(Ghost(cb_inst), 0, Tracked(cb_head)));
        let cb_inst = Tracked(cyclic_buffer_instance.clone());
        let ul_inst = Tracked(unbounded_log_instance.clone());
        let tail = CachePadded(
            AtomicU64::new(Ghost((cb_inst, ul_inst)), 0, Tracked((ul_tail, cb_tail))),
        );
        let mut local_versions: Vec<
            CachePadded<
                AtomicU64<
                    (Tracked<UnboundedLog::Instance<DT>>, Tracked<CyclicBuffer::Instance<DT>>, int),
                    (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>),
                    _,
                >,
            >,
        > = Vec::with_capacity(num_replicas);
        let mut nid = 0;
        while nid < num_replicas
            invariant
                0 <= nid <= num_replicas,
                local_versions.len() == nid,
                forall|i| nid <= i < num_replicas ==> ul_local_versions.contains_key(i),
                forall|i| nid <= i < num_replicas ==> cb_local_versions.contains_key(i),
                forall|i|
                    #![trigger cb_local_versions[i]]
                    nid <= i < num_replicas ==> {
                        &&& cb_local_versions[i]@.instance == cyclic_buffer_instance
                        &&& cb_local_versions[i]@.key == i
                        &&& cb_local_versions[i]@.value == 0
                    },
                forall|i|
                    #![trigger ul_local_versions[i]]
                    nid <= i < num_replicas ==> {
                        &&& ul_local_versions[i]@.instance == unbounded_log_instance
                        &&& ul_local_versions[i]@.key == i
                        &&& ul_local_versions[i]@.value == 0
                    },
                forall|i: int|
                    #![trigger local_versions[i]]
                    0 <= i < local_versions.len() ==> {
                        &&& local_versions[i].0.well_formed()
                        &&& local_versions[i].0.constant().0 == unbounded_log_instance
                        &&& local_versions[i].0.constant().1 == cyclic_buffer_instance
                        &&& local_versions[i].0.constant().2 == i
                    },
        {
            let ghost mut nid_ghost;
            let tracked ul_version;
            let tracked cb_version;
            proof {
                nid_ghost = nid as int;
                ul_version = ul_local_versions.tracked_remove(nid as nat);
                cb_version = cb_local_versions.tracked_remove(nid as nat);
            }
            let cb_inst = Tracked(cyclic_buffer_instance.clone());
            let ul_inst = Tracked(unbounded_log_instance.clone());
            local_versions.push(
                CachePadded(
                    AtomicU64::new(
                        Ghost((ul_inst, cb_inst, nid_ghost)),
                        0,
                        Tracked((ul_version, cb_version)),
                    ),
                ),
            );
            nid = nid + 1;
        }
        //
        // Create the replica tokens
        //

        let mut replica_tokens: Vec<ReplicaToken> = Vec::with_capacity(num_replicas);
        let mut idx = 0;
        while idx < num_replicas
            invariant
                0 <= idx <= num_replicas,
                num_replicas <= MAX_REPLICAS,
                replica_tokens.len() == idx,
                forall|i|
                    #![trigger replica_tokens[i]]
                    0 <= i < idx ==> replica_tokens[i].id_spec() == i,
        {
            replica_tokens.push(ReplicaToken::new(idx as ReplicaId));
            idx = idx + 1;
        }
        let ghost mut num_replicas_ghost;
        proof { num_replicas_ghost = num_replicas as nat }
        ;
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
            num_replicas: Ghost(num_replicas as nat),
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
        };
        (log, replica_tokens, Tracked(config))
    }

    /// Returns a physical index given a logical index into the shared log.
    #[inline(always)]
    pub(crate) fn index(&self, logical: u64) -> (result: usize)
        requires
            self.slog.len() == LOG_SIZE,
        ensures
            result as nat == self.index_spec(logical as nat),
            result == log_entry_idx(logical as int, self.slog.len() as nat),
            result < self.slog.len(),
    {
        (logical as usize) % self.slog.len()
    }

    pub  /*REVIEW: (crate)*/
     open spec fn index_spec(&self, logical: nat) -> nat
        recommends
            self.slog.len() == LOG_SIZE,
    {
        logical % (self.slog.len() as nat)
    }

    #[inline(always)]
    pub(crate) fn is_alive_value(&self, logical: u64) -> (result: bool)
        requires
            self.slog.len() == LOG_SIZE,
        ensures
            result == self.is_alive_value_spec(logical as int),
            result == log_entry_alive_value(logical as int, self.slog.len() as nat),
    {
        ((logical as usize) / LOG_SIZE % 2) == 0
    }

    pub  /*REVIEW: (crate)*/
     open spec fn is_alive_value_spec(&self, logical: int) -> bool
        recommends
            self.slog.len() == LOG_SIZE,
    {
        ((logical / (LOG_SIZE as int)) % 2) == 0
    }

    /// This method returns the current version upper bound value for the log.
    ///
    ///  - Rust: get_ctail()
    ///  - Dafny: n/a part of do-read
    pub(crate) fn get_version_upper_bound(
        &self,
        local_reads: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (ret: (u64, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            local_reads@@.instance == self.unbounded_log_instance@,
            local_reads@@.value.is_Init(),
        ensures
            ret.1@@.value.is_VersionUpperBound(),
            ret.1@@.value.get_VersionUpperBound_version_upper_bound() == ret.0 as nat,
            ret.1@@.value.get_VersionUpperBound_op() == local_reads@@.value.get_Init_op(),
            ret.1@@.instance == self.unbounded_log_instance@,
            ret.1@@.key == local_reads@@.key,
    {
        let tracked local_reads = local_reads.get();
        let ghost rid = local_reads@.key;
        let tracked new_local_reads_g: UnboundedLog::local_reads<DT>;
        let res =
            atomic_with_ghost!(
            &self.version_upper_bound.0 => load();
            returning res;
            ghost g => {
                new_local_reads_g = self.unbounded_log_instance.borrow()
                                            .readonly_version_upper_bound(rid, &g, local_reads);
            }
        );
        (res, Tracked(new_local_reads_g))
    }

    /// checks whether the version of the local replica has advanced enough to perform read operations
    ///
    /// This basically corresponds to the transition `readonly_read_to_read` in the unbounded log.
    ///
    // https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/log.rs#L525
    pub fn is_replica_synced_for_reads(
        &self,
        node_id: ReplicaId,
        version_upper_bound: u64,
        local_reads: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: (bool, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            node_id < self.local_versions.len(),
            local_reads@@.instance == self.unbounded_log_instance@,
            local_reads@@.value.is_VersionUpperBound(),
            local_reads@@.value.get_VersionUpperBound_version_upper_bound() == version_upper_bound,
        ensures
            result.0 ==> result.1@@.value.is_ReadyToRead(),
            result.0 ==> result.1@@.value.get_ReadyToRead_node_id() == node_id,
            result.0 ==> result.1@@.value.get_ReadyToRead_op()
                == local_reads@@.value.get_VersionUpperBound_op(),
            !result.0 ==> result.1 == local_reads,
            result.1@@.instance == self.unbounded_log_instance@,
            result.1@@.key == local_reads@@.key,
    {
        // obtain the request id from the local_reads token
        let rid_g: Ghost<ReqId> = Ghost(local_reads@@.key);
        let tracked new_local_reads_g: UnboundedLog::local_reads<DT>;
        // obtain the local version
        let local_version = &self.local_versions[node_id as usize].0;
        let res =
            atomic_with_ghost!(
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

    proof fn unbounded_log_append_entries(
        tracked &self,
        nid: nat,
        ridx: nat,
        tracked state: AppendEntriesGhostState<DT>,
    ) -> (tracked ret: AppendEntriesGhostState<DT>)
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
        decreases ridx,
    {
        let tracked mut state = state;
        if ridx != 0 {
            state = self.unbounded_log_append_entries(nid, (ridx - 1) as nat, state);
        }
        let tracked AppendEntriesGhostState {
            idx,
            old_tail,
            mut log_entries,
            mut local_updates,
            combiner,
            mut tail,
            request_ids,
            operations,
        } = state;
        // get the local update and the
        let reqid = request_ids[ridx as int];
        let tracked local_update = local_updates.tracked_remove(ridx);
        let tracked update_result =
            self.unbounded_log_instance.borrow().update_place_ops_in_log_one(
            nid as nat,
            reqid,
            &mut tail,
            local_update,
            combiner,
        );
        let tracked combiner = update_result.2.get();
        log_entries.tracked_insert(ridx, update_result.0.get());
        local_updates.tracked_insert(ridx, update_result.1.get());
        let tracked res = AppendEntriesGhostState {
            idx: idx + 1,
            old_tail,
            log_entries,
            local_updates,
            combiner,
            tail,
            request_ids,
            operations,
        };
        res
    }

    /// Inserts a slice of operations into the log.
    #[inline(always)]
    pub fn append(
        &self,
        replica_token: &ReplicaToken,
        operations: &Vec<DT::WriteOperation>,
        // responses and actual replica are part of the closure
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        // here we also need to pass the mut replica
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>,
    ) -> (result: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            old(actual_replica).inv(),
            replica_token@ < self.local_versions.len(),
            old(responses).len() == 0,
            ghost_data@.append_pre(
                replica_token@,
                old(actual_replica).view(),
                operations@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
            operations.len() <= MAX_REQUESTS,
        ensures
            actual_replica.inv(),
            result@.append_post(
                ghost_data@,
                replica_token@,
                actual_replica.view(),
                operations@,
                responses@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
    {
        let tracked mut ghost_data_new = ghost_data.get();
        let nid = replica_token.id() as usize;
        let nops = operations.len();
        let mut iteration = 1;
        let mut waitgc = 1;
        loop
            invariant
                self.wf(),
                actual_replica.inv(),
                0 <= waitgc <= WARN_THRESHOLD,
                0 <= iteration <= WARN_THRESHOLD,
                responses.len() == 0,
                replica_token@ < self.local_versions.len(),
                nid == replica_token@,
                nops == operations.len(),
                nops <= MAX_REQUESTS,
                ghost_data_new.cb_combiner@@.value == ghost_data@.cb_combiner@@.value,
                ghost_data_new.request_ids@ == ghost_data@.request_ids@,
                ghost_data_new.append_pre(
                    replica_token@,
                    actual_replica.view(),
                    operations@,
                    self.unbounded_log_instance@,
                    self.cyclic_buffer_instance@,
                ),
        {
            // unpack stuff
            let tracked NrLogAppendExecDataGhost {
                local_updates,
                ghost_replica,
                combiner,
                cb_combiner,
                request_ids,
            } = ghost_data_new;
            let tracked mut cb_combiner = cb_combiner.get();
            let tracked mut combiner = combiner.get();
            let tracked mut local_updates = local_updates.get();
            if iteration == WARN_THRESHOLD {
                print_starvation_warning(line!());
                iteration = 0;
            }
            iteration = iteration + 1;
            // let tail = self.tail.load(Ordering::Relaxed);
            let tail =
                atomic_with_ghost!(
                &self.tail.0 => load();
                returning tail;
                ghost g => { }
            );
            // let head = self.head.load(Ordering::Relaxed);
            let head =
                atomic_with_ghost!(
                &self.head.0 => load();
                returning tail;
                ghost g => {
                    cb_combiner = self.cyclic_buffer_instance.borrow()
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
                }
                waitgc = waitgc + 1;
                proof {
                    cb_combiner =
                    self.cyclic_buffer_instance.borrow().advance_tail_abort(
                        nid as nat,
                        cb_combiner,
                    );
                }
                // overwrite the request_ids here, as we're not executing any local updates
                let tracked ghost_data0 = NrLogAppendExecDataGhost {
                    local_updates: Tracked(local_updates),
                    ghost_replica,
                    combiner: Tracked(combiner),
                    cb_combiner: Tracked(cb_combiner),
                    request_ids: Ghost(Seq::empty()),
                };
                let ghost_data0 = self.execute(
                    replica_token,
                    responses,
                    actual_replica,
                    Tracked(ghost_data0),
                );
                let tracked ghost_data0 = ghost_data0.get();
                proof {
                    ghost_data_new =
                    NrLogAppendExecDataGhost {
                        local_updates: ghost_data0.local_updates,
                        ghost_replica: ghost_data0.ghost_replica,
                        combiner: ghost_data0.combiner,
                        cb_combiner: ghost_data0.cb_combiner,
                        request_ids,
                    };
                }
                // upstream has an advance_head here, but dafny doesn't
                // let ghost_data0 = self.advance_head(replica_token, responses, actual_replica, ghost_data0);
                continue ;
            }
            let new_tail = tail + (nops as u64);
            // capture the warning here
            if new_tail >= MAX_IDX {
                warn_with_tail_too_big();
                ////////////////////////////////////////////////////////////////////////////////////
                // !!! THIS IS A PANIC CASE! WE DO NOT RETURN FROM HERE !!!
                ////////////////////////////////////////////////////////////////////////////////////
                #[allow(while_true)]
                while true {
                }  // TODO: is that fine?

            }
            // If on adding in the above entries there would be fewer than `GC_FROM_HEAD`
            // entries left on the log, then we need to advance the head of the log.

            let advance = new_tail > head + (self.slog.len() - GC_FROM_HEAD) as u64;
            // Try reserving slots for the operations. If that fails, then restart
            // from the beginning of this loop.
            // if self.tail.compare_exchange_weak(tail, tail + nops, Ordering::Acquire, Ordering::Acquire) !+ Ok(tail) {
            //     continue;
            // }
            let tracked mut cb_log_entries: Map<int, StoredType<DT>> = Map::tracked_empty();
            let tracked mut log_entries: Map<nat, UnboundedLog::log<DT>> = Map::tracked_empty();
            let result =
                atomic_with_ghost!(
                //&self.tail.0 => compare_exchange(tail, new_tail);
                &self.tail.0 => compare_exchange_weak(tail, new_tail);
                update prev -> next;
                returning result;
                ghost g => {
                    if matches!(result, Result::Ok(tail)) {
                        let tracked (mut unbounded_tail, mut cb_tail) = g;

                        let tracked (_, Tracked(cb_log_entries0), Tracked(cb_combiner0))
                             = self.cyclic_buffer_instance.borrow()
                                .advance_tail_finish(nid as nat, new_tail as nat, &mut cb_tail, cb_combiner);

                        cb_combiner = cb_combiner0;
                        cb_log_entries = cb_log_entries0;

                        // transition to the placed phase
                        combiner = self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);

                        if request_ids.view().len() > 0 {
                            let tracked append_entries_ghost_state = AppendEntriesGhostState {
                                idx : 0,
                                old_tail: tail as nat,
                                log_entries,
                                local_updates,
                                combiner,
                                tail: unbounded_tail,
                                request_ids: request_ids.view(),
                                operations: operations.view()
                            };

                            let tracked append_entries_ghost_state = self.unbounded_log_append_entries(nid as nat, (request_ids.view().len() - 1) as nat, append_entries_ghost_state);
                            log_entries = append_entries_ghost_state.log_entries;
                            combiner = append_entries_ghost_state.combiner;
                            unbounded_tail = append_entries_ghost_state.tail;
                            local_updates = append_entries_ghost_state.local_updates;
                            assert(combiner@.value.get_Placed_queued_ops() =~= request_ids@);
                        } else {
                            assert(combiner@.value.get_Placed_queued_ops() =~= request_ids@);
                        }

                        g = (unbounded_tail, cb_tail);
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
                    ghost_data_new =
                    NrLogAppendExecDataGhost {
                        local_updates: Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                        ghost_replica,  // Tracked<UnboundedLog::replicas>,
                        combiner: Tracked(combiner),  // Tracked<UnboundedLog::combiner>,
                        cb_combiner: Tracked(cb_combiner),  // Tracked<CyclicBuffer::combiner>,
                        request_ids,  // Ghost<Seq<ReqId>>,
                    };
                }
                continue ;
            }
            let ghost cell_ids = self.cyclic_buffer_instance@.cell_ids();
            let ghost buffer_size = self.cyclic_buffer_instance@.buffer_size();
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
                    buffer_size == LOG_SIZE,
                    cell_ids == self.cyclic_buffer_instance@.cell_ids(),
                    cell_ids.len() == buffer_size,
                    cb_combiner@.key == nid,
                    cb_combiner@.value.is_Appending(),
                    cb_combiner@.value.get_Appending_cur_idx() == tail + idx,
                    cb_combiner@.value.get_Appending_tail() == new_tail,
                    cb_combiner@.value.get_Appending_cur_idx()
                        <= cb_combiner@.value.get_Appending_tail(),
                    cb_combiner@.instance == self.cyclic_buffer_instance@,
                    forall|i|
                        #![trigger log_entries[i]]
                        idx <= i < request_ids@.len() ==> {
                            &&& (#[trigger] log_entries.contains_key(i))
                            &&& log_entries[i]@.key == tail + i
                            &&& log_entries[i]@.instance == self.unbounded_log_instance@
                            &&& log_entries[i]@.value.node_id
                                == nid as nat
                            //
                            // The following will result in a resource limit exceeded
                            //

                            &&& log_entries[i]@.value.op
                                == operations[i as int]
                            //
                            // Adding the `&` below will fix this.
                            //
                            // &&& log_entries[i]@.value.op == &operations[i as int]

                        },
                    forall|i|
                        (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE
                            <==> cb_log_entries.contains_key(i),
                    forall|i|
                        cb_log_entries.contains_key(i) ==> stored_type_inv(
                            #[trigger] cb_log_entries.index(i),
                            i,
                            cell_ids[log_entry_idx(i, buffer_size) as int],
                            self.unbounded_log_instance@,
                        ),
            {
                let tracked cb_log_entry;
                proof {
                    cb_log_entry = cb_log_entries.tracked_remove((tail + idx) - LOG_SIZE);
                }
                let tracked mut cb_log_entry_perms = cb_log_entry.cell_perms;
                // the logical index into the log
                let logical_log_idx = tail + idx as u64;
                let log_idx = self.index(logical_log_idx);
                // unsafe { (*e).operation = Some(op.clone()) };
                // unsafe { (*e).replica = idx.0 };
                let new_log_entry = ConcreteLogEntry {
                    op: DT::clone_write_op(&operations[idx as usize]),
                    node_id: nid as u64,
                };
                // update the log entry in the buffer
                self.slog[log_idx].log_entry.replace(
                    Tracked(&mut cb_log_entry_perms),
                    Option::Some(new_log_entry),
                );
                // unsafe { (*e).alivef.store(m, Ordering::Release) };
                let m = self.is_alive_value(logical_log_idx as u64);
                atomic_with_ghost!(
                    &self.slog[log_idx].alive => store(m);
                    ghost g => {
                        let tracked new_stored_type = StoredType {
                            cell_perms: cb_log_entry_perms,
                            log_entry: Option::Some(log_entries.tracked_remove(idx as nat)),
                        };

                        let tracked (Tracked(alive_bit), Tracked(cb_combiner0))
                            = self.cyclic_buffer_instance.borrow()
                            .append_flip_bit(nid as NodeId, new_stored_type, new_stored_type, g, cb_combiner);

                        g = alive_bit;
                        cb_combiner = cb_combiner0;
                    }
                );
                idx = idx + 1;
            }
            assert(forall|i|
                #![trigger log_entries[i]]
                idx <= i < request_ids@.len() ==> {
                    &&& #[trigger] log_entries.contains_key(i)
                    &&& log_entries[i]@.key == tail + i
                    &&& log_entries[i]@.instance == self.unbounded_log_instance@
                    &&& log_entries[i]@.value.node_id == nid as nat
                    &&& log_entries[i]@.value.op == operations[i as int]
                });
            assert(forall|i|
                (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE <==> cb_log_entries.contains_key(
                    i,
                ));
            assert(forall|i|
                cb_log_entries.contains_key(i) ==> stored_type_inv(
                    #[trigger] cb_log_entries.index(i),
                    i,
                    cell_ids[log_entry_idx(i, buffer_size) as int],
                    self.unbounded_log_instance@,
                ));
            proof {
                cb_combiner =
                self.cyclic_buffer_instance.borrow().append_finish(nid as nat, cb_combiner);
                ghost_data_new =
                NrLogAppendExecDataGhost {
                    local_updates: Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                    ghost_replica,  // Tracked<UnboundedLog::replicas>,
                    combiner: Tracked(combiner),  // Tracked<UnboundedLog::combiner>,
                    cb_combiner: Tracked(cb_combiner),  // Tracked<CyclicBuffer::combiner>,
                    request_ids,  // Ghost<Seq<ReqId>>,
                };
            }
            if advance {
                let ghost_data_new = self.advance_head(
                    replica_token,
                    responses,
                    actual_replica,
                    Tracked(ghost_data_new),
                );
                return ghost_data_new;
            } else {
                return Tracked(ghost_data_new);
            }
        }
    }

    /// Advances the head of the log forward. If a replica has stopped making
    /// progress, then this method will never return. Accepts a closure that is
    /// passed into execute() to ensure that this replica does not deadlock GC.
    #[inline(always)]
    fn advance_head(
        &self,
        replica_token: &ReplicaToken,
        // the following were part of the closure
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        // ghost state for execute etc.
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>,
    ) -> (res: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            old(actual_replica).inv(),
            replica_token.wf(self.num_replicas@),
            ghost_data@.advance_head_pre(
                replica_token.id_spec(),
                old(actual_replica).view(),
                old(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
        ensures
            actual_replica.inv(),
            res@.advance_head_post(
                ghost_data@,
                replica_token.id_spec(),
                actual_replica.view(),
                responses@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
    {
        let mut ghost_data_new = ghost_data;
        let mut iteration = 1;
        loop
            invariant
                self.wf(),
                actual_replica.inv(),
                replica_token.wf(self.num_replicas@),
                ghost_data_new@.cb_combiner@@.value.is_Idle(),
                ghost_data_new@.combiner@@.value.is_Placed() ==> ghost_data_new@.pre_exec(
                    responses@,
                ),
                ghost_data_new@.advance_head_post(
                    ghost_data@,
                    replica_token.id_spec(),
                    actual_replica.view(),
                    responses@,
                    self.unbounded_log_instance@,
                    self.cyclic_buffer_instance@,
                ),
                0 <= iteration <= WARN_THRESHOLD,
        {
            let Tracked(ghost_data0) = ghost_data_new;
            let tracked NrLogAppendExecDataGhost {
                local_updates,
                ghost_replica,
                combiner,
                cb_combiner,
                request_ids,
            } = ghost_data0;
            let tracked mut cb_combiner = cb_combiner.get();
            // let global_head = self.head.load(Ordering::Relaxed);
            let global_head =
                atomic_with_ghost!(
                &self.head.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );
            // let f = self.tail.load(Ordering::Relaxed);
            let global_tail =
                atomic_with_ghost!(
                &self.tail.0 => load();
                returning ret;
                ghost g => { /* no-op */ }
            );
            let (min_local_version, cb_combiner0) = self.find_min_local_version(
                Tracked(cb_combiner),
            );
            let tracked mut cb_combiner = cb_combiner0.get();
            // If we cannot advance the head further, then start
            // from the beginning of this loop again. Before doing so, try consuming
            // any new entries on the log to prevent deadlock.
            if min_local_version == global_head {
                proof {
                    cb_combiner =
                    self.cyclic_buffer_instance.borrow().advance_head_abort(
                        replica_token.id_spec(),
                        cb_combiner,
                    );
                }
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    // let tracked cb_combiner = Tracked(cb_combiner);
                    // let tracked ghost_data = NrLogAppendExecDataGhost { local_updates, ghost_replica, combiner, cb_combiner, request_ids };
                    // return Tracked(ghost_data);
                    iteration = 0;
                }
                let cb_combiner = Tracked(cb_combiner);
                let tracked ghost_data0 = NrLogAppendExecDataGhost {
                    local_updates,
                    ghost_replica,
                    combiner,
                    cb_combiner,
                    request_ids,
                };
                ghost_data_new =
                self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
                continue ;
            }
            // There are entries that can be freed up; update the head offset.
            // self.head.store(min_local_tail, Ordering::Relaxed);

            atomic_with_ghost!(
                &self.head.0 => store(min_local_version);
                update old_val -> new_val;
                ghost g => {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_head_finish(replica_token.id_spec(), &mut g, cb_combiner);
            });
            if global_tail < min_local_version + self.slog.len() as u64 - GC_FROM_HEAD as u64 {
                let cb_combiner = Tracked(cb_combiner);
                let tracked ghost_data_new = NrLogAppendExecDataGhost {
                    local_updates,
                    ghost_replica,
                    combiner,
                    cb_combiner,
                    request_ids,
                };
                return Tracked(ghost_data_new);
            }
            let cb_combiner = Tracked(cb_combiner);
            let tracked ghost_data0 = NrLogAppendExecDataGhost {
                local_updates,
                ghost_replica,
                combiner,
                cb_combiner,
                request_ids,
            };
            // replica_token@ < self.local_versions.len(),
            ghost_data_new =
            self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
        }
    }

    /// proof function that transitions local updates into the done state.
    proof fn execute_update_done_multiple(
        tracked &self,
        request_ids: Seq<ReqId>,
        tracked local_updates: Map<nat, UnboundedLog::local_updates<DT>>,
        tracked version_upper_bound: &UnboundedLog::version_upper_bound<DT>,
    ) -> (tracked res: Map<nat, UnboundedLog::local_updates<DT>>)
        requires
            self.wf(),
            version_upper_bound@.instance == self.unbounded_log_instance@,
            forall|i|
                #![trigger local_updates[i]]
                0 <= i < request_ids.len() ==> {
                    &&& #[trigger] local_updates.contains_key(i)
                    &&& local_updates[i]@.key == request_ids[i as int]
                    &&& local_updates[i]@.instance == self.unbounded_log_instance@
                    &&& local_updates[i]@.value.is_Applied()
                    &&& local_updates[i]@.value.get_Applied_idx() < version_upper_bound@.value
                },
        ensures
            forall|i|
                #![trigger res[i]]
                0 <= i < request_ids.len() ==> {
                    &&& #[trigger] res.contains_key(i)
                    &&& res[i]@.key == request_ids[i as int]
                    &&& res[i]@.instance == self.unbounded_log_instance@
                    &&& res[i]@.value.is_Done()
                    &&& res[i]@.value.get_Done_ret() == local_updates[i]@.value.get_Applied_ret()
                },
        decreases request_ids.len(),
    {
        if request_ids.len() == 0 {
            return local_updates;
        }
        let tracked mut local_updates_new = local_updates;
        let idx = (request_ids.len() - 1) as nat;
        let tracked local_update = local_updates_new.tracked_remove(idx);
        local_updates_new =
        self.execute_update_done_multiple(
            request_ids.subrange(0, request_ids.len() - 1),
            local_updates_new,
            version_upper_bound,
        );
        let tracked update_done_result = self.unbounded_log_instance.borrow().update_done(
            request_ids.last(),
            version_upper_bound,
            local_update,
        );
        local_updates_new.tracked_insert(idx, update_done_result);
        return local_updates_new;
    }

    /// Executes a passed in closure (`d`) on all operations starting from a
    /// replica's local tail on the shared log. The replica is identified
    /// through an `idx` passed in as an argument.
    pub(crate) fn execute(
        &self,
        replica_token: &ReplicaToken,
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>,
    ) -> (result: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            old(actual_replica).inv(),
            self.wf(),
            replica_token@ < self.local_versions.len(),
            ghost_data@.execute_pre(
                replica_token@,
                old(actual_replica).view(),
                old(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
        ensures
            actual_replica.inv(),
            result@.execute_post(
                ghost_data@,
                replica_token@,
                actual_replica.view(),
                old(responses)@,
                responses@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
    {
        let nid = replica_token.id() as usize;
        // somehow can't really do this as a destructor
        let tracked ghost_data = ghost_data.get();
        // let tracked Tracked(ghost_data) = ghost_data;  // XXX: that one here doesn't work?
        let tracked mut local_updates = ghost_data.local_updates.get();  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
        let tracked mut ghost_replica = ghost_data.ghost_replica.get();  // Tracked<UnboundedLog::replicas>,
        let tracked mut combiner = ghost_data.combiner.get();  // Tracked<UnboundedLog::combiner>,
        let tracked mut cb_combiner = ghost_data.cb_combiner.get();  // Tracked<CyclicBuffer::combiner>,
        let ghost request_ids = ghost_data.request_ids@;  // Ghost<Seq<ReqId>>,
        let ghost mut request_ids_new = request_ids;
        proof {
            // if the combiner in idle, we start it with the trival start transition
            if combiner@.value.is_Ready() {
                combiner =
                self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);
                request_ids_new = Seq::empty();
            }
        }
        // let ltail = self.ltails[idx.0 - 1].load(Ordering::Relaxed);
        let mut local_version =
            atomic_with_ghost!(
            &self.local_versions[nid].0 => load();
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
        let global_tail =
            atomic_with_ghost!(
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
            let tracked ghost_data_ret = NrLogAppendExecDataGhost {
                local_updates: Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
                ghost_replica: Tracked(ghost_replica),  // Tracked<UnboundedLog::replicas>,
                combiner: Tracked(combiner),  // Tracked<UnboundedLog::combiner>,
                cb_combiner: Tracked(cb_combiner),  // Tracked<CyclicBuffer::combiner>,
                request_ids: Ghost(request_ids),  // Ghost<Seq<ReqId>>,
            };
            // not sure why this one needs to be here?
            assert(ghost_data_ret.common_pred(
                replica_token@,
                actual_replica.view(),
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ));
            // assert(ghost_data_ret.cb_combiner@@.value  == ghost_data.cb_combiner@@.value);
            // assert(ghost_data_ret.request_ids == ghost_data.request_ids);
            // assert(ghost_data.combiner@@.value.is_Placed() ==> {
            //     &&& ghost_data_ret.post_exec(ghost_data.request_ids@, responses@)
            // });
            // assert(ghost_data.combiner@@.value.is_Ready() ==> {
            //     &&& ghost_data_ret.combiner@@.value  == ghost_data.combiner@@.value
            //     &&& ghost_data_ret.local_updates == ghost_data.local_updates
            //     &&& responses@ == old(responses)@
            // });
            // assert(ghost_data_ret.execute_post(ghost_data, replica_token@, actual_replica.view(), old(responses)@, responses@, self.unbounded_log_instance@, self.cyclic_buffer_instance@));
            return Tracked(ghost_data_ret);
        }
        // Execute all operations from the passed in offset to the shared log's tail.
        // Check if the entry is live first; we could have a replica that has reserved
        // entries, but not filled them into the log yet.
        // for i in ltail..gtail {

        let ghost local_updates_old = local_updates;
        let ghost responses_old = responses@;
        let mut responses_idx: usize = 0;
        while local_version < global_tail
            invariant
                self.wf(),
                actual_replica.inv(),
                ghost_data.combiner@@.value.is_Placed() ==> {
                    &&& ghost_data.combiner@@.value.get_Placed_queued_ops() == request_ids
                    &&& combiner@.value.get_Loop_queued_ops() == request_ids
                },
                ghost_data.combiner@@.value.is_Ready() ==> combiner@.value.get_Loop_queued_ops()
                    == Seq::<ReqId>::empty(),
                combiner@.value.queued_ops() == request_ids_new,
                0 <= local_version <= global_tail,
                0 <= responses_idx as nat <= request_ids_new.len(),
                responses_idx == 0 ==> responses@ == responses_old && local_updates
                    == local_updates_old,
                ghost_data.combiner@@.value.is_Placed() ==> responses.len() == responses_idx,
                request_ids_new.len() <= MAX_REQUESTS,
                ghost_replica@.instance == self.unbounded_log_instance@,
                ghost_replica@.key == nid as nat,
                ghost_replica@.value == actual_replica.view(),
                cb_combiner@.key == nid as nat,
                cb_combiner@.instance == self.cyclic_buffer_instance@,
                cb_combiner@.value.is_Reading(),
                cb_combiner@.value.get_Reading_0().is_Range(),
                cb_combiner@.value.get_Reading_0().get_Range_cur() == local_version,
                cb_combiner@.value.get_Reading_0().get_Range_end() == global_tail,
                combiner@.key == nid as nat,
                combiner@.instance == self.unbounded_log_instance@,
                combiner@.value.is_Loop(),
                combiner@.value.get_Loop_queued_ops() == request_ids_new,
                combiner@.value.get_Loop_lversion() == local_version,
                combiner@.value.get_Loop_tail() == global_tail,
                combiner@.value.get_Loop_idx() == responses_idx,
                forall|i|
                    #![trigger local_updates[i]]
                    responses_idx <= i < request_ids_new.len() ==> {
                        &&& #[trigger ] local_updates.contains_key(i)
                        &&& local_updates[i]@.key == request_ids_new[i as int]
                        &&& local_updates[i]@.value.is_Placed()
                        &&& local_updates[i]@.instance == self.unbounded_log_instance@
                    },
                ghost_data.combiner@@.value.is_Placed() ==> forall|i|
                    #![trigger local_updates[i]]
                    0 <= i < responses_idx ==> {
                        &&& #[trigger] local_updates.contains_key(i)
                        &&& local_updates[i]@.key == request_ids_new[i as int]
                        &&& local_updates[i]@.instance == self.unbounded_log_instance@
                        &&& local_updates[i]@.value.is_Applied()
                        &&& local_updates[i]@.value.get_Applied_ret() == responses[i as int]
                        &&& local_updates[i]@.value.get_Applied_idx()
                            < combiner@.value.get_Loop_tail()
                    },
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
                    actual_replica.inv(),
                    local_version < global_tail,
                    phys_log_idx < self.slog.len(),
                    phys_log_idx as nat == self.index_spec(local_version as nat),
                    is_alive_value == self.is_alive_value_spec(local_version as int),
                    0 <= iteration <= WARN_THRESHOLD,
                    cb_combiner@.instance == self.cyclic_buffer_instance@,
                    cb_combiner@.key == nid as nat,
                    cb_combiner@.value.is_Reading(),
                    !is_alive ==> cb_combiner@.value.get_Reading_0().is_Range(),
                    !is_alive ==> cb_combiner@.value.get_Reading_0().get_Range_cur()
                        == local_version,
                    !is_alive ==> cb_combiner@.value.get_Reading_0().get_Range_end() == global_tail,
                    is_alive ==> cb_combiner@.value.get_Reading_0().is_Guard(),
                    is_alive ==> cb_combiner@.value.get_Reading_0().get_Guard_cur()
                        == local_version,
                    is_alive ==> cb_combiner@.value.get_Reading_0().get_Guard_end() == global_tail,
                    self.slog.spec_index(phys_log_idx as int).wf(
                        phys_log_idx as nat,
                        self.cyclic_buffer_instance@,
                    ),
            {
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    iteration = 0;
                }
                let alive_bit =
                    atomic_with_ghost!(
                    &self.slog[phys_log_idx].alive => load();
                    returning alive_bit;
                    ghost g => {
                        if alive_bit == is_alive_value {
                            let tracked (_, Tracked(cb_combiner0)) =
                                self.cyclic_buffer_instance.borrow().reader_guard(nid as nat, &g, cb_combiner);
                            cb_combiner = cb_combiner0;
                        }
                    });
                is_alive = alive_bit == is_alive_value;
                iteration = iteration + 1;
            }
            // dispatch the operation to apply the update to the replica
            // unsafe { d((*e).operation.as_ref().unwrap().clone(),(*e).replica == idx.0,) };

            let tracked stored_entry: &StoredType<DT>;
            proof {
                stored_entry =
                self.cyclic_buffer_instance.borrow().guard_guards(nid as nat, &cb_combiner);
            }
            // read the entry
            let log_entry = self.slog[phys_log_idx].log_entry.borrow(
                Tracked(&stored_entry.cell_perms),
            );
            // perform the update
            let res = actual_replica.dispatch_mut(
                DT::clone_write_op(&log_entry.as_ref().unwrap().op),
            );
            if log_entry.as_ref().unwrap().node_id == nid as u64 {
                // case: local dispatch, store the result in the response vector
                proof {
                    // unwrap the entry
                    if let Option::Some(e) = &stored_entry.log_entry {
                        // appeal to the state machien to get that response_idx < request_ids_new.len()
                        self.unbounded_log_instance.borrow().pre_exec_dispatch_local(
                            nid as nat,
                            e,
                            &combiner,
                        );
                        let tracked local_update = local_updates.tracked_remove(
                            responses_idx as nat,
                        );
                        let tracked (
                            Tracked(ghost_replica0),
                            Tracked(local_update),
                            Tracked(combiner0),
                        ) = self.unbounded_log_instance.borrow().exec_dispatch_local(
                            nid as nat,
                            e,
                            ghost_replica,
                            local_update,
                            combiner,
                        );
                        ghost_replica = ghost_replica0;
                        local_updates.tracked_insert(responses_idx as nat, local_update);
                        combiner = combiner0;
                    } else {
                        assert(false);
                    }
                }
                responses.push(res);
                responses_idx = responses_idx + 1;
            } else {
                // case: remote dispatch
                proof {
                    assert(stored_entry.log_entry.get_Some_0().view().value.node_id != nid);
                    if let Option::Some(e) = &stored_entry.log_entry {
                        assert(e.view().value.node_id != nid);
                        // assert(ghost_replica@.key == nid as nat);
                        // assert(combiner@.value.get_Loop_lversion() < combiner@.value.get_Loop_tail());
                        let tracked exec_dispatch_remote_result =
                            self.unbounded_log_instance.borrow().exec_dispatch_remote(
                            nid as nat,
                            e,
                            ghost_replica,
                            combiner,
                        );
                        ghost_replica = exec_dispatch_remote_result.0.get();
                        combiner = exec_dispatch_remote_result.1.get();
                    } else {
                        assert(false)  // should not happen

                    }
                }
            }
            proof {
                cb_combiner =
                self.cyclic_buffer_instance.borrow().reader_unguard(nid as nat, cb_combiner);
            }
            local_version = local_version + 1;
        }
        proof {
            self.unbounded_log_instance.borrow().pre_exec_update_version_upper_bound(
                nid as nat,
                &combiner,
            );
        }
        // self.ctail.fetch_max(gtail, Ordering::Relaxed);
        atomic_with_ghost!(
            &self.version_upper_bound.0 => fetch_max(global_tail);
            ghost g => {
                combiner = self.unbounded_log_instance.borrow().exec_update_version_upper_bound(nid as nat, &mut g, combiner);

                if ghost_data.combiner@@.value.is_Placed() {
                    local_updates = self.execute_update_done_multiple(request_ids_new,  local_updates, &g);
                }
            });
        // self.ltails[idx.0 - 1].store(gtail, Ordering::Relaxed);
        atomic_with_ghost!(
            &self.local_versions[nid].0 => store(global_tail);
            ghost g => {
                let tracked (Tracked(ul_local_versions), Tracked(ul_combiner))
                    = self.unbounded_log_instance.borrow().exec_finish(nid as nat, g.0, combiner);
                let tracked (Tracked(cb_local_versions), Tracked(cb_combiner0))
                    = self.cyclic_buffer_instance.borrow().reader_finish(nid as nat, g.1, cb_combiner);

                combiner = ul_combiner;
                cb_combiner = cb_combiner0;

                g = (ul_local_versions, cb_local_versions);
        });
        let tracked ghost_data_ret = NrLogAppendExecDataGhost {
            local_updates: Tracked(local_updates),  // Tracked::<Map<ReqId, UnboundedLog::local_updates>>,
            ghost_replica: Tracked(ghost_replica),  // Tracked<UnboundedLog::replicas>,
            combiner: Tracked(combiner),  // Tracked<UnboundedLog::combiner>,
            cb_combiner: Tracked(cb_combiner),  // Tracked<CyclicBuffer::combiner>,
            request_ids: Ghost(request_ids),  // Ghost<Seq<ReqId>>,
        };
        // not sure why this one needs to be here?
        assert(ghost_data_ret.execute_post(
            ghost_data,
            replica_token@,
            actual_replica.view(),
            old(responses)@,
            responses@,
            self.unbounded_log_instance@,
            self.cyclic_buffer_instance@,
        ));
        Tracked(ghost_data_ret)
    }

    /// Loops over all `local_versions` and finds the replica with the lowest version.
    ///
    /// # Returns
    /// The ID (in `LogToken`) of the replica with the lowest tail and the
    /// corresponding/lowest tail `idx` in the `Log`.
    ///
    ///  - Dafny: part of advance_head
    pub(crate) fn find_min_local_version(
        &self,
        cb_combiner: Tracked<CyclicBuffer::combiner<DT>>,
    ) -> (result: (u64, Tracked<CyclicBuffer::combiner<DT>>))
        requires
            self.wf(),
            cb_combiner@@.instance == self.cyclic_buffer_instance@,
            cb_combiner@@.value.is_Idle(),
        ensures
            result.0 <= MAX_IDX,
            result.1@@.key == cb_combiner@@.key,
            result.1@@.value.is_AdvancingHead(),
            result.1@@.instance == self.cyclic_buffer_instance@,
            result.1@@.value.get_AdvancingHead_idx() == self.num_replicas,
            result.1@@.value.get_AdvancingHead_min_local_version() == result.0,
    {
        // let r = self.next.load(Ordering::Relaxed);
        let num_replicas = self.local_versions.len();
        let tracked mut g_cb_comb_new: CyclicBuffer::combiner<DT> = cb_combiner.get();
        let ghost g_node_id = cb_combiner@@.key;
        // let (mut min_replica_idx, mut min_local_tail) = (0, self.ltails[0].load(Ordering::Relaxed));
        let mut min_local_version =
            atomic_with_ghost!(
            &self.local_versions[0].0 => load();
            returning ret;
            ghost g => {
                g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                        .advance_head_start(g_node_id, &g.1, g_cb_comb_new);
            });
        // Find the smallest local tail across all replicas.
        // for idx in 1..r {
        //    let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
        //    min_local_tail = min(min_local_tail, cur_local_tail)
        //}
        let mut idx: usize = 1;
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
                num_replicas == self.local_versions.len(),
        {
            // let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
            let cur_local_tail =
                atomic_with_ghost!(
                &self.local_versions[idx].0 => load();
                returning ret;
                ghost g => {
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
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost State
////////////////////////////////////////////////////////////////////////////////////////////////////
/// Data structure that is passed between the append and exec functins of the log.
pub tracked struct NrLogAppendExecDataGhost<DT: Dispatch> {
    pub  /* REVIEW (crate) */
     local_updates: Tracked::<Map<ReqId, UnboundedLog::local_updates<DT>>>,
    pub  /* REVIEW (crate) */
     ghost_replica: Tracked<UnboundedLog::replicas<DT>>,
    pub  /* REVIEW (crate) */
     combiner: Tracked<UnboundedLog::combiner<DT>>,
    pub  /* REVIEW (crate) */
     cb_combiner: Tracked<CyclicBuffer::combiner<DT>>,
    pub  /* REVIEW (crate) */
     request_ids: Ghost<Seq<ReqId>>,
}

impl<DT: Dispatch> NrLogAppendExecDataGhost<DT> {
    /// some common predicate that ties the state to the node and instances
    pub open spec fn common_pred(
        &self,
        nid: NodeId,
        data: DT::View,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& (forall|i|
            0 <= i < self.request_ids@.len() ==> {
                &&& (#[trigger] self.local_updates@.contains_key(i))
                &&& self.local_updates@[i]@.instance == inst
            })
        &&& self.ghost_replica@@.key == nid
        &&& self.ghost_replica@@.instance == inst
        &&& self.ghost_replica@@.value == data
        &&& self.combiner@@.key == nid
        &&& self.combiner@@.instance == inst
        &&& self.cb_combiner@@.key == nid
        &&& self.cb_combiner@@.instance == cb_inst
        &&& self.request_ids@.len() <= MAX_REQUESTS
    }

    pub open spec fn append_pre(
        &self,
        nid: NodeId,
        data: DT::View,
        ops: Seq<DT::WriteOperation>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& (forall|i|
            #![trigger self.local_updates@[i]]
            0 <= i < self.request_ids@.len() ==> {
                &&& #[trigger] self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
                &&& self.local_updates@[i]@.value.is_Init()
                &&& self.local_updates@[i]@.value.get_Init_op() == ops[i as int]
            })
        &&& self.combiner@@.value.is_Ready()
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.request_ids@.len() == ops.len()
    }

    pub open spec fn append_post(
        &self,
        pre: Self,
        nid: NodeId,
        data: DT::View,
        operations: Seq<DT::WriteOperation>,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.is_Ready() ==> self.post_exec(pre.request_ids@, responses)
        &&& self.combiner@@.value.is_Placed() ==> self.pre_exec(responses)
        &&& self.cb_combiner@@.value
            == pre.cb_combiner@@.value  // other fields in common_pred

        &&& self.request_ids == pre.request_ids
    }

    pub open spec fn execute_pre(
        &self,
        nid: NodeId,
        data: DT::View,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.is_Placed() ==> self.pre_exec(responses)
        &&& self.combiner@@.value.is_Ready() ==> {
            &&& self.request_ids@.len() == responses.len()
        }
    }

    pub open spec fn execute_post(
        &self,
        pre: Self,
        nid: NodeId,
        data: DT::View,
        responses_old: Seq<DT::Response>,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.cb_combiner@@.value == pre.cb_combiner@@.value
        &&& self.request_ids == pre.request_ids
        &&& pre.combiner@@.value.is_Placed() ==> {
            &&& self.post_exec(pre.request_ids@, responses)
        }
        &&& pre.combiner@@.value.is_Ready() ==> {
            &&& self.combiner@@.value == pre.combiner@@.value
            &&& self.local_updates == pre.local_updates
            &&& responses == responses_old
        }
    }

    pub open spec fn advance_head_pre(
        &self,
        nid: NodeId,
        data: DT::View,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.pre_exec(responses)
        &&& self.cb_combiner@@.value.is_Idle()
        &&& self.combiner@@.value.is_Placed()
    }

    pub open spec fn advance_head_post(
        &self,
        pre: Self,
        nid: NodeId,
        data: DT::View,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.request_ids == pre.request_ids
        &&& self.cb_combiner@@.value == pre.cb_combiner@@.value
        &&& self.combiner@@.value.is_Ready() || self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.is_Ready() ==> {
            &&& self.post_exec(self.request_ids@, responses)
        }
        &&& self.combiner@@.value.is_Placed() ==> {
            &&& responses.len() == 0
            &&& self.local_updates == pre.local_updates
            &&& self.combiner@@.value == pre.combiner@@.value
            &&& self.ghost_replica@@.value == pre.ghost_replica@@.value
        }
    }

    // corresponds to Dafny's pre_exec() function
    pub open spec fn pre_exec(&self, responses: Seq<DT::Response>) -> bool {
        &&& responses.len() == 0
        &&& self.combiner@@.value.is_Placed()
        &&& self.combiner@@.value.get_Placed_queued_ops() == self.request_ids
        &&& (forall|i|
            #![trigger self.local_updates@[i]]
            0 <= i < self.request_ids@.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.key == self.request_ids@[i as int]
                &&& self.local_updates@[i]@.value.is_Placed()
            })
    }

    // corresponds to Dafny's post_exec() function
    pub open spec fn post_exec(
        &self,
        request_ids: Seq<ReqId>,
        responses: Seq<DT::Response>,
    ) -> bool {
        &&& request_ids.len() == responses.len()
        &&& self.combiner@@.value.is_Ready()
        &&& (forall|i|
            #![trigger self.local_updates@[i]]
            0 <= i < request_ids.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i]@.value.is_Done()
                &&& self.local_updates@[i]@.value.get_Done_ret() == responses[i as int]
                &&& self.local_updates@[i]@.key == request_ids[i as int]
            })
    }
}

struct_with_invariants!{
/// keeps track of the recursive state when applying updates to the unbounded log
tracked struct AppendEntriesGhostState<DT: Dispatch> {
    pub ghost idx               : nat,
    pub ghost old_tail          : nat,
    pub tracked log_entries     : Map<nat, UnboundedLog::log<DT>>,
    pub tracked local_updates   : Map<nat, UnboundedLog::local_updates<DT>>,
    pub tracked combiner        : UnboundedLog::combiner<DT>,
    pub tracked tail            : UnboundedLog::tail<DT>,
    pub ghost request_ids       : Seq<ReqId>,
    pub ghost operations        : Seq<<DT as Dispatch>::WriteOperation>
}

pub open spec fn wf(&self, nid: nat, ridx: nat, inst: UnboundedLog::Instance<DT>) -> bool {
    predicate {
        &&& 0 <= self.idx <= self.request_ids.len()
        &&& ridx < self.request_ids.len()

        &&& self.tail@.value == self.old_tail + self.idx
        &&& self.tail@.instance == inst

        &&& self.combiner@.instance == inst
        &&& self.combiner@.key == nid
        &&& self.combiner@.value.is_Placed()
        &&& self.combiner@.value.get_Placed_queued_ops().len() == self.idx

        &&& (forall |i| 0 <= i < self.idx ==> #[trigger]self.request_ids[i] == self.combiner@.value.get_Placed_queued_ops()[i])

        // we added all the new entries
        &&& (forall |i| 0 <= i < self.idx <==> self.log_entries.contains_key(i))
        &&& (forall |i| 0 <= i < self.request_ids.len() ==> self.local_updates.contains_key(i))

        // processed entries
        &&& (forall |i| #![trigger self.local_updates[i]] 0 <= i < self.idx ==> {
            &&& self.local_updates[i]@.instance == inst
            &&& self.local_updates[i]@.key == self.request_ids[i as int]
            &&& self.local_updates[i]@.value.is_Placed()
            &&& self.local_updates[i]@.value.get_Placed_op() == self.operations[i as int]
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
}  // struct_with_invariants!


struct_with_invariants!{
/// represents the tokens that are created when a new log is being initialized
pub tracked struct NrLogTokens<DT: Dispatch> {
    pub ghost num_replicas: nat,
    pub tracked replicas                : Map<NodeId,UnboundedLog::replicas<DT>>,
    pub tracked combiners               : Map<NodeId,UnboundedLog::combiner<DT>>,
    pub tracked cb_combiners            : Map<NodeId, CyclicBuffer::combiner<DT>>,
    pub tracked unbounded_log_instance  : UnboundedLog::Instance<DT>,
    pub tracked cyclic_buffer_instance  : CyclicBuffer::Instance<DT>,
}

pub open spec fn wf(&self, num_replicas: nat) -> bool {
    predicate {
        &&& self.num_replicas == num_replicas
        &&& self.unbounded_log_instance.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance.num_replicas() == self.num_replicas
        &&& (forall |i| #![trigger self.replicas[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.replicas.contains_key(i)
            &&& self.replicas[i]@.instance == self.unbounded_log_instance
            &&& self.replicas[i]@.key == i
            &&& self.replicas[i]@.value == DT::init_spec()
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

}  // struct_with_invariants!{


} // verus!
