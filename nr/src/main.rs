// the verus dependencies

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use vstd::{
    cell::{CellId, PCell, PointsTo},
    map::Map,
    option::Option,
    prelude::*,
    vec::Vec,
    atomic_ghost::*,
    pervasive::*,
    *,
};

// use pervasive::slice::slice_index_set;

mod spec;
mod exec;
mod constants;

use constants::{NUM_REPLICAS, LOG_SIZE, MAX_THREADS_PER_REPLICA};

// spec imports
use spec::{
    cyclicbuffer::{CyclicBuffer},
    types::*,
    unbounded_log::UnboundedLog,
};

// exec imports
use crate::exec::log::{NrLog, NrLogTokens};
use crate::exec::replica::{Replica, ReplicaConfig, ReplicaId};
use crate::exec::context::ThreadToken;

verus! {



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
    pub/*REVIEW: (crate)*/ log: NrLog,
    // log: NrLog,

    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<DataStructureType, UpdateOp, ReturnType>>>,
    pub/*REVIEW: (crate)*/ replicas: Vec<Box<Replica>>,

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
            &&& self.replicas[i].replica_token@ == i
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
    pub fn new(num_replicas: usize) -> (res: Self)
        requires
            num_replicas == NUM_REPLICAS
        ensures res.wf()
    {
        let (log, replica_tokens, nr_log_tokens) = NrLog::new(num_replicas, LOG_SIZE);

        let tracked NrLogTokens {
            num_replicas: _,
            replicas: mut replicas,
            combiners: mut combiners,
            cb_combiners: mut cb_combiners,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = nr_log_tokens.get();

        let mut actual_replicas : Vec<Box<Replica>> = Vec::new();
        let mut idx = 0;
        while idx < num_replicas
            invariant
                num_replicas <= NUM_REPLICAS,
                0 <= idx <= num_replicas,
                replica_tokens.len() == num_replicas,
                forall |i| 0 <= i < num_replicas ==> (#[trigger]replica_tokens[i]).id_spec() == i,
                actual_replicas.len() == idx,
                forall |i| #![trigger actual_replicas[i]] 0 <= i < idx ==> {
                    &&& actual_replicas[i as int].wf()
                    &&& actual_replicas[i as int].spec_id() == i
                    &&& actual_replicas[i as int].unbounded_log_instance@ == unbounded_log_instance
                    &&& actual_replicas[i as int].cyclic_buffer_instance@ == cyclic_buffer_instance
                },
                (forall |i| #![trigger replicas[i]] idx <= i < num_replicas ==> {
                    &&& #[trigger]  replicas.contains_key(i)
                    &&& replicas[i]@.instance == unbounded_log_instance
                    &&& replicas[i]@.key == i
                    &&& replicas[i]@.value == DataStructureSpec::init()
                }),
                (forall |i| #![trigger combiners[i]] idx <= i < num_replicas ==> {
                    &&& #[trigger] combiners.contains_key(i)
                    &&& combiners[i]@.instance == unbounded_log_instance
                    &&& combiners[i]@.key == i
                    &&& combiners[i]@.value.is_Ready()
                }),
                (forall |i| #![trigger cb_combiners[i]] idx <= i < num_replicas ==> {
                    &&& #[trigger]cb_combiners.contains_key(i)
                    &&& cb_combiners[i]@.instance == cyclic_buffer_instance
                    &&& cb_combiners[i]@.key == i
                    &&& cb_combiners[i]@.value.is_Idle()
                })

        {
            let ghost mut idx_ghost; proof { idx_ghost = idx as nat };

            let tracked combiner = combiners.tracked_remove(idx_ghost);
            let tracked cb_combiner = cb_combiners.tracked_remove(idx_ghost);
            let tracked replica = replicas.tracked_remove(idx_ghost);
            let replica_token = replica_tokens.index(idx).clone();
            let tracked config = ReplicaConfig {
                replica,
                combiner,
                cb_combiner,
                unbounded_log_instance: unbounded_log_instance.clone(),
                cyclic_buffer_instance: cyclic_buffer_instance.clone(),
            };
            assert(config.wf(idx as nat));
            assert(replica_token.id_spec() == idx as nat);

            let replica = Replica::new(replica_token, MAX_THREADS_PER_REPLICA, Tracked(config));
            actual_replicas.push(Box::new(replica));
            idx = idx + 1;
        }

        let unbounded_log_instance = Tracked(unbounded_log_instance);
        let cyclic_buffer_instance = Tracked(cyclic_buffer_instance);
        NodeReplicated { log, replicas: actual_replicas, unbounded_log_instance, cyclic_buffer_instance }
    }

    /// Registers a thread with a given replica in the [`NodeReplicated`]
    /// data-structure. Returns an Option containing a [`ThreadToken`] if the
    /// registration was successful. None if the registration failed.
    ///
    /// XXX: in the dafny version, we don't have this. Instead, we pre-allocate all
    ///      threads for the replicas etc.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken>
    pub fn register(&mut self, replica_id: ReplicaId) -> Option<ThreadToken>
        requires old(self).wf()
    {
        if (replica_id as usize) < self.replicas.len() {
            None
        } else {
            None
        }
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
            tkn.batch_perm@@.pcell == self.replicas.spec_index(tkn.replica_id_spec() as int).contexts.spec_index(tkn.thread_id_spec() as int).batch.0.id(),
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
            tkn.batch_perm@@.pcell == self.replicas.spec_index(tkn.replica_id_spec() as int).contexts.spec_index(tkn.thread_id_spec() as int).batch.0.id(),
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






} // verus!

use  std::sync::Arc;

struct NrCounter(Arc<NodeReplicated>, ThreadToken);

const NUM_OPS_PER_THREAD: usize = 1000;
const NUM_THREADS: usize = 4;

// #[verifier(external_body)] /* vattr */
#[verifier::external_body] /* vattr */
pub fn main() {

    println!("Creating Replicated Data Structure...");

    let mut nr_counter = NodeReplicated::new(NUM_REPLICAS);

    println!("Obtaining Thread tokens for {NUM_THREADS} threads...");

    let mut thread_tokens = Vec::with_capacity(NUM_THREADS);
    for idx in 0..NUM_THREADS+NUM_REPLICAS {
        if let Option::Some(tkn) = nr_counter.register(idx % NUM_REPLICAS) {
            thread_tokens.push(tkn);
        } else {
            panic!("could not register with replica!");
        }
    }

    let nr_counter = Arc::new(nr_counter);

    // The replica executes a Modify or Access operations by calling
    // `execute_mut` and `execute`. Eventually they end up in the `Dispatch` trait.
    let thread_loop = |counter: NrCounter| {
        let NrCounter(counter, mut tkn) = counter;
        let tid = tkn.thread_id();
        println!("Thread #{tid}  executing {NUM_OPS_PER_THREAD} operations");
        for i in 0..NUM_OPS_PER_THREAD {
            match i % 2 {
                0 => {
                    match counter.execute_mut(UpdateOp::Inc, tkn) {
                        Result::Ok((ret, t)) => {
                            tkn = t;
                        },
                        Result::Err(t) => {
                            tkn = t;
                        }
                    }
                }
                1 => {
                    match  counter.execute(ReadonlyOp::Get, tkn) {
                        Result::Ok((ret, t)) => {
                            tkn = t;
                        },
                        Result::Err(t) => {
                            tkn = t;
                        }
                    }
                }
                _ => unreachable!(),
            };
        }
    };

    println!("Creating {NUM_THREADS} threads...");

    let mut threads = Vec::with_capacity(NUM_THREADS);
    for idx in 0..NUM_THREADS {
        let counter = nr_counter.clone();
        let tkn = thread_tokens.pop();
        threads.push(std::thread::spawn(move || {
            thread_loop(NrCounter(counter, tkn));
        }));
    }

    println!("Waiting for threads to finish...");

    // Wait for all the threads to finish
    for idx in 0..NUM_THREADS {
        let thread = threads.pop();
        thread.join().unwrap();
    }

    println!("Obtain final result...");

    for idx in 0 .. NUM_REPLICAS {
        let tkn = thread_tokens.pop();
        match nr_counter.execute(ReadonlyOp::Get, tkn) {
            Result::Ok((ret, t)) => {
                match ret {
                    ReturnType::Value(v) => {
                        println!("Replica {idx} - Final Result: v expected {}", NUM_THREADS * NUM_OPS_PER_THREAD / 2);
                    }
                    ReturnType::Ok => {
                        println!("Replica {idx} - Final Result: OK? expected {}", NUM_THREADS * NUM_OPS_PER_THREAD / 2);
                    }
                }
            },
            Result::Err(t) => {
                println!("Replica {idx} - Final Result: Err");
            }
        }
    }

    println!("Done!");
}
