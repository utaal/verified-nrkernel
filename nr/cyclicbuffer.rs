


////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Cyclic Buffer
// =============
//
// Dafny: https://github.com/secure-foundations/iron-sync/blob/concurrency-experiments/concurrency/node-replication/CyclicBuffer.i.dfy
////////////////////////////////////////////////////////////////////////////////////////////////////





////////////////////////////////////////////////////////////////////////////////////////////////////
//
////////////////////////////////////////////////////////////////////////////////////////////////////




// datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)

pub struct ConcreteLogEntry {
    op: u8, // TODO: make this something sensible,  UpdateOp?
    node_id: u64,
}

// glinear datatype StoredType = StoredType(
//   glinear cellContents: CellContents<ConcreteLogEntry>,
//   glinear logEntry: glOption<Log>
// )
use  std::cell::Cell;
pub struct StoredType {
    cell_contents: Cell<ConcreteLogEntry>,
    log_entry: Option<u8>,
}

// datatype ReaderState =
//   | ReaderStarting(ghost start: nat)
//   | ReaderRange(ghost start: nat, ghost end: nat, ghost cur: nat)
//   | ReaderGuard(ghost start: nat, ghost end: nat, ghost cur: nat, ghost val: StoredType)

pub enum ReaderState {
    Starting(nat),
    Range { start: nat, end: nat, cur: nat},
    Guard { start: nat, end: nat, cur: nat, val: StoredType },
}

// datatype CombinerState =
//   | CombinerIdle
//   | CombinerReading(ghost readerState: ReaderState)
//   | CombinerAdvancingHead(ghost idx: nat, ghost min_tail: nat)
//   | CombinerAdvancingTail(ghost observed_head: nat)
//   | CombinerAppending(ghost cur_idx: nat, ghost tail: nat)

pub enum CombinerState {
    Idle,
    Reading(ReaderState),
    AdvancingHead{idx:NodeId, min_tail:nat},
    AdvancingTail{observed_head: nat},
    Appending{cur_idx: nat, tail: nat},
}




tokenized_state_machine!{

    CyclicBuffer {
        fields {
            /// the number of nodes this cyclic buffer log is configured for
            #[sharding(constant)]
            pub num_nodes: nat,

            /// the size of the log in elements
            #[sharding(constant)]
            pub log_size: nat,

            // the log content,
            // TODO: should we just use an array here?
            #[sharding(variable)]
            pub log: Map<int, StoredType>,

            // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
            // and sometimes 'false' means 'alive'.
            // entry is an index into the buffer (0 <= entry < LOG_SIZE)
            #[sharding(map)]
            pub log_alive_bits: Map<nat, bool>,

            // Logical index into the above slice at which the log starts.
            // NOTE: the tail _does not_ monotonically advances. It's only guaranteed to be <= all the local tails.
            #[sharding(variable)]
            pub version_upper_bound: nat,

            // Logical index into the above slice at which the log ends.
            // New appends go here.
            #[sharding(variable)]
            pub global_tail: nat,

            // Array consisting of the local tail of each replica registered with the log.
            // Required for garbage collection; since replicas make progress over the log
            // independently, we want to make sure that we don't garbage collect operations
            // that haven't been executed by all replicas.
            #[sharding(map)]
            pub local_heads: Map<NodeId, nat>,


            #[sharding(map)]
            pub local_reads: Map<NodeId, ReadonlyState>,

            #[sharding(map)]
            pub local_updates: Map<NodeId, UpdateState>,

            // the combiner state fo reach node
            #[sharding(map)]
            pub combiner: Map<NodeId, CombinerState>
        }

        /// State Machine Initialization
        init!{
            initialize(num_replicas: nat, log_size: nat) {
                // && s.head == Some(0)
                init version_upper_bound = 0;
                // && s.tail == Some(0)
                init global_tail = 0;
                // the size of the log
                init log_size = log_size;
                // the number of nodes
                init num_nodes = num_replicas;
                // && (s.localTails    == map x : nat | x < (NUM_REPLICAS as nat) :: 0 as nat)
                init local_heads = Map::new(|i| i < (num_replicas as nat), |_| 0 as nat);
                // && (s.combinerState == map x : nat | x < (NUM_REPLICAS as nat) :: CombinerIdle)
                init combiner = Map::new(|i| i < (num_replicas as nat), |_| CombinerState::Idle);
                // && (s.aliveBits     == map x : nat | x < LOG_SIZE as nat :: x := LogicalToAliveBitAliveWhen(x - LOG_SIZE as int))
                init alive_bits = Map::new(|i| i < (log_size as nat), |i|  logical_idx_to_alive_bit(i - log_size));
                // && s.contents.Some?
                // && (forall i: int :: -(LOG_SIZE as int) <= i < 0 <==> (i in s.contents.value))
                init contents = Some(Map::new(|i| -log_size <= i < 0, |_|  StoredType{cell_contents: CellContents::Empty, log_entry: None}));
            }
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        // Readonly Operation
        ////////////////////////////////////////////////////////////////////////////////////////////

        transition!{

        }




        ////////////////////////////////////////////////////////////////////////////////////////////
        // Update Operations
        ////////////////////////////////////////////////////////////////////////////////////////////




        transition! {
            init_advance_head(nid: NodeId) {
                //&& LocalTailValid(m, 0)
                //&& CombinerKnown(m, combinerNodeId)
                //&& CombinerIsIdle(m, combinerNodeId)

                // the combiner is in idle state and the local head is known
                have combiner >= [ nid => CombinerState::Idle ];
                have local_heads >= [ node_id => let local_head ];

                //&& m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerAdvancingHead(1, m.localTails[0])])
                add combiner += [ nid => CombinerState::AdvancingHead{idx:1, min_tail: local_head} ];
            }

        }





        ////////////////////////////////////////////////////////////////////////////////////////////
        // Log Indexing
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// we could make a type for the log index here...
        fn logical_idx_to_alive_bit(&self, logical: LogIdx) -> bool
        {
            ((logical / self.log_size) % 2) == 0
        }
    }
}


