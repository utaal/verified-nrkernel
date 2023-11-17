#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

// spec imports
use crate::spec::{
    cyclicbuffer::CyclicBuffer,
    types::*,
    unbounded_log::UnboundedLog,
};

// exec imports
use crate::exec::log::{NrLog, NrLogTokens};
use crate::exec::replica::{Replica, ReplicaConfig, ReplicaId};
use crate::exec::context::ThreadToken;

use crate::constants::{NUM_REPLICAS, LOG_SIZE, MAX_THREADS_PER_REPLICA};

pub mod rwlock;
pub mod log;
pub mod replica;
pub mod context;
pub mod utils;

/// a simpe cache padding for the struct fields
#[repr(align(128))]
pub struct CachePadded<T>(pub T);

verus! {


////////////////////////////////////////////////////////////////////////////////////////////////////
// The Public Interface
////////////////////////////////////////////////////////////////////////////////////////////////////


/// The "main" type of NR which users interact with.
///
///  - Dafny: N/A
///  - Rust:  pub struct NodeReplicated<D: Dispatch + Sync>
pub struct NodeReplicated<DT: Dispatch> {
    /// the log of operations
    ///
    ///  - Rust: log: Log<D::WriteOperation>,
    pub /* REVIEW: (crate) */ log: NrLog<DT>,
    // log: NrLog,

    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<DataStructureType, UpdateOp, ReturnType>>>,
    pub /* REVIEW (crate) */ replicas: Vec<Box<Replica<DT>>>,


    pub /* REVIEW: (crate) */ thread_tokens: Vec<Vec<ThreadToken<DT>>>,

    /// XXX: should that be here, or go into the NrLog / replicas?
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}


/// Proof blocks for the NodeReplicate data structure
impl<DT: Dispatch> NodeReplicated<DT> {
    /// Wellformedness of the NodeReplicated data structure
    pub open spec fn wf(&self) -> bool {
        // the log shall be well-formed and the instances match
        &&& self.log.wf()
        &&& self.unbounded_log_instance@ == self.log.unbounded_log_instance@
        &&& self.cyclic_buffer_instance@ == self.log.cyclic_buffer_instance@

        // the number of replicas should be the as configured
        &&& self.replicas.len() == NUM_REPLICAS

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


impl<DT: Dispatch> NodeReplicated<DT> {
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

        let mut actual_replicas : Vec<Box<Replica<DT>>> = Vec::new();
        let mut thread_tokens : Vec<Vec<ThreadToken<DT>>> = Vec::new();
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
                    &&& replicas[i]@.value == DT::init_spec()
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
            let replica_token = replica_tokens[idx].clone();
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
        NodeReplicated { log, replicas: actual_replicas, thread_tokens, unbounded_log_instance, cyclic_buffer_instance }
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
    pub fn register(&mut self, replica_id: ReplicaId) -> Option<ThreadToken<DT>>
        requires old(self).wf()
        // ensures self.wf()
    {
        if (replica_id as usize) < self.replicas.len() {
            let mut replica : Box<Replica<DT>> = self.replicas.remove(replica_id);
            let res : Option<ThreadToken<DT>> = (*replica).register();
            self.replicas.insert(replica_id, replica);
            res
        } else {
            Option::None
        }
    }

    /// Executes a mutable operation against the data-structure.
    ///
    ///  - Dafny:
    ///  - Rust:  pub fn execute_mut(&self, op: <D as Dispatch>::WriteOperation, tkn: ThreadToken)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    pub fn execute_mut(&self, op: DT::WriteOperation, tkn: ThreadToken<DT>) -> Result<(DT::Response, ThreadToken<DT>), ThreadToken<DT>>
        requires
            self.wf() && tkn.wf(),
            tkn.fc_client@@.instance == self.replicas.spec_index(tkn.replica_id_spec() as int).flat_combiner_instance,
            tkn.batch_perm@@.pcell == self.replicas.spec_index(tkn.replica_id_spec() as int).contexts.spec_index(tkn.thread_id_spec() as int).batch.0.id(),
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            (&self.replicas[replica_id]).execute_mut(&self.log, op, tkn)
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
    pub fn execute(&self, op: DT::ReadOperation, tkn: ThreadToken<DT>) -> Result<(DT::Response, ThreadToken<DT>), ThreadToken<DT>>
        requires
            self.wf() && tkn.wf(),
            tkn.fc_client@@.instance == self.replicas.spec_index(tkn.replica_id_spec() as int).flat_combiner_instance,
            tkn.batch_perm@@.pcell == self.replicas.spec_index(tkn.replica_id_spec() as int).contexts.spec_index(tkn.thread_id_spec() as int).batch.0.id(),
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            (&self.replicas[replica_id]).execute(&self.log, op, tkn)
        } else {
            Err(tkn)
        }
    }
}

} // verus!
