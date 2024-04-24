#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

use crate::Dispatch;

// spec imports
use crate::spec::{cyclicbuffer::CyclicBuffer, unbounded_log::UnboundedLog};

// exec imports
use crate::exec::context::ThreadToken;
use crate::exec::log::{NrLog, NrLogTokens};
use crate::exec::replica::{Replica, ReplicaConfig, ReplicaId};

use crate::constants::{LOG_SIZE, MAX_REPLICAS, MAX_THREADS_PER_REPLICA};
use crate::AffinityFn;

pub mod context;
pub mod log;
pub mod replica;
pub mod rwlock;
pub mod utils;

verus! {

/// a simpe cache padding for the struct fields
#[verus::trusted]
#[repr(align(128))]
pub struct CachePadded<T>(pub T);

////////////////////////////////////////////////////////////////////////////////////////////////////
// The Public Interface
////////////////////////////////////////////////////////////////////////////////////////////////////
/// The "main" type of NR which users interact with.
///
///  - Dafny: N/A
///  - Rust:  pub struct NodeReplicated<D: Dispatch + Sync>
#[verifier::reject_recursive_types(DT)]
pub struct NodeReplicated<DT: Dispatch> {
    /// the log of operations
    ///
    ///  - Rust: log: Log<D::WriteOperation>,
    pub  /* REVIEW: (crate) */
     log: NrLog<DT>,
    // log: NrLog,
    /// the nodes or replicas in the system
    ///
    ///  - Rust: replicas: Vec<Box<Replica<D>>>,
    // replicas: Vec<Box<Replica<DataStructureType, UpdateOp, ReturnType>>>,
    pub  /* REVIEW (crate) */
     replicas: Vec<Box<Replica<DT>>>,
    // pub /* REVIEW: (crate) */ thread_tokens: Vec<Vec<ThreadToken<DT>>>,
    /// XXX: should that be here, or go into the NrLog / replicas?
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}

impl<DT: Dispatch> crate::ThreadTokenT<DT, Replica<DT>> for ThreadToken<DT> {
    open spec fn wf(&self, replica: &Replica<DT>) -> bool {
        ThreadToken::<DT>::wf(self, replica)
    }

    open spec fn replica_id_spec(&self) -> nat {
        ThreadToken::<DT>::replica_id_spec(self)
    }
}

impl<DT: Dispatch + Sync> crate::NodeReplicatedT<DT> for NodeReplicated<DT> {
    type Replica = Replica<DT>;

    type ReplicaId = ReplicaId;

    type TT = ThreadToken<DT>;

    /// Wellformedness of the NodeReplicated data structure
    open spec fn wf(&self) -> bool {
        // the log shall be well-formed and the instances match
        &&& self.log.wf()
        &&& self.unbounded_log_instance@ == self.log.unbounded_log_instance@
        &&& self.cyclic_buffer_instance@
            == self.log.cyclic_buffer_instance@
        // the number of replicas should be the as configured

        &&& self.replicas.len()
            <= MAX_REPLICAS
        // the replicas should be well-formed and the instances match

        &&& (forall|i|
            0 <= i < self.replicas.len() ==> {
                &&& (#[trigger] self.replicas[i]).wf()
                &&& self.replicas[i].spec_id() == i
                &&& self.replicas[i].replica_token@ == i
                &&& self.replicas[i].unbounded_log_instance@ == self.unbounded_log_instance@
                &&& self.replicas[i].cyclic_buffer_instance@ == self.cyclic_buffer_instance@
            })
    }

    open spec fn replicas(&self) -> Vec<Box<Self::Replica>> {
        self.replicas
    }

    open spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT> {
        self.log.unbounded_log_instance@
    }

    /// Creates a new, replicated data-structure from a single-threaded
    /// data-structure that implements [`Dispatch`]. It uses the [`Default`]
    /// constructor to create a initial data-structure for `D` on all replicas.
    ///
    ///  - Dafny: n/a ?
    ///  - Rust:  pub fn new(num_replicas: NonZeroUsize) -> Result<Self, NodeReplicatedError>
    fn new(num_replicas: usize, chg_mem_affinity: AffinityFn) -> (res:
        Self)
    // requires
    //     num_replicas <= MAX_REPLICAS
    // ensures res.wf()
    {
        // switch affinity to the first replica
        chg_mem_affinity.call(0);
        let (log, replica_tokens, nr_log_tokens) = NrLog::new(num_replicas, LOG_SIZE);
        let tracked NrLogTokens {
            num_replicas: _,
            replicas: mut replicas,
            combiners: mut combiners,
            cb_combiners: mut cb_combiners,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = nr_log_tokens.get();
        let mut actual_replicas: Vec<Box<Replica<DT>>> = Vec::new();
        let mut thread_tokens: Vec<Vec<ThreadToken<DT>>> = Vec::new();
        let mut idx = 0;
        while idx < num_replicas
            invariant
                num_replicas <= MAX_REPLICAS,
                unbounded_log_instance.num_replicas() == num_replicas,
                cyclic_buffer_instance.num_replicas() == num_replicas,
                cyclic_buffer_instance.unbounded_log_instance() == unbounded_log_instance,
                0 <= idx <= num_replicas,
                replica_tokens.len() == num_replicas,
                forall|i| 0 <= i < num_replicas ==> (#[trigger] replica_tokens[i]).id_spec() == i,
                actual_replicas.len() == idx,
                forall|i|
                    #![trigger actual_replicas[i]]
                    0 <= i < idx ==> {
                        &&& actual_replicas[i as int].wf()
                        &&& actual_replicas[i as int].spec_id() == i
                        &&& actual_replicas[i as int].unbounded_log_instance@
                            == unbounded_log_instance
                        &&& actual_replicas[i as int].cyclic_buffer_instance@
                            == cyclic_buffer_instance
                    },
                (forall|i|
                    #![trigger replicas[i]]
                    idx <= i < num_replicas ==> {
                        &&& #[trigger] replicas.contains_key(i)
                        &&& replicas[i]@.instance == unbounded_log_instance
                        &&& replicas[i]@.key == i
                        &&& replicas[i]@.value == DT::init_spec()
                    }),
                (forall|i|
                    #![trigger combiners[i]]
                    idx <= i < num_replicas ==> {
                        &&& #[trigger] combiners.contains_key(i)
                        &&& combiners[i]@.instance == unbounded_log_instance
                        &&& combiners[i]@.key == i
                        &&& combiners[i]@.value.is_Ready()
                    }),
                (forall|i|
                    #![trigger cb_combiners[i]]
                    idx <= i < num_replicas ==> {
                        &&& #[trigger] cb_combiners.contains_key(i)
                        &&& cb_combiners[i]@.instance == cyclic_buffer_instance
                        &&& cb_combiners[i]@.key == i
                        &&& cb_combiners[i]@.value.is_Idle()
                    }),
        {
            let ghost mut idx_ghost;
            proof { idx_ghost = idx as nat }
            ;
            let replica_token = replica_tokens[idx].clone();
            let tracked config = ReplicaConfig {
                replica: replicas.tracked_remove(idx_ghost),
                combiner: combiners.tracked_remove(idx_ghost),
                cb_combiner: cb_combiners.tracked_remove(idx_ghost),
                unbounded_log_instance: unbounded_log_instance.clone(),
                cyclic_buffer_instance: cyclic_buffer_instance.clone(),
            };
            // switch the affinity of the replica before we do the allocation
            chg_mem_affinity.call(replica_token.id());
            let replica = Replica::new(replica_token, MAX_THREADS_PER_REPLICA, Tracked(config));
            actual_replicas.push(Box::new(replica));
            idx = idx + 1;
        }
        // change the affinity back

        chg_mem_affinity.call(0);
        let unbounded_log_instance = Tracked(unbounded_log_instance);
        let cyclic_buffer_instance = Tracked(cyclic_buffer_instance);
        NodeReplicated {
            log,
            replicas: actual_replicas,
            unbounded_log_instance,
            cyclic_buffer_instance,
        }
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
    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<
        ThreadToken<DT>,
    >)
    // requires old(self).wf()
    // ensures
    //     self.wf(),
    //     result.is_Some() ==> result.get_Some_0().WF(&self.replicas[replica_id as int])
    {
        if (replica_id as usize) < self.replicas.len() {
            let mut replica: Box<Replica<DT>> = self.replicas.remove(replica_id);
            let res: Option<ThreadToken<DT>> = (*replica).register();
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
    fn execute_mut(
        &self,
        op: DT::WriteOperation,
        tkn: ThreadToken<DT>,
        ticket: Tracked<UnboundedLog::local_updates<DT>>,
    ) -> (result: Result<
        (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>),
        (ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>),
    >)
    // requires
    //     self.wf(), // wf global node
    //     tkn.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
    //     is_update_ticket(ticket@, op, self.log.unbounded_log_instance@)
    // ensures
    //     result.is_Ok() ==> is_update_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.log.unbounded_log_instance@) && result.get_Ok_0().1.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
    //     result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            Ok((&self.replicas[replica_id]).execute_mut(&self.log, op, tkn, ticket))
        } else {
            Err((tkn, ticket))
        }
    }

    /// Executes a immutable operation against the data-structure.
    ///
    ///  - Dafny: N/A (in c++ code?)
    ///  - Rust:  pub fn execute(&self, op: <D as Dispatch>::ReadOperation<'_>, tkn: ThreadToken,)
    ///             -> <D as Dispatch>::Response
    ///
    /// This is basically a wrapper around the `do_operation` of the interface defined in Dafny
    fn execute(
        &self,
        op: DT::ReadOperation,
        tkn: ThreadToken<DT>,
        ticket: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: Result<
        (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>),
        (ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>),
    >)
    // requires
    //     self.wf(), // wf global node
    //     tkn.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
    //     is_readonly_ticket(ticket@, op, self.log.unbounded_log_instance@)
    // ensures
    //     result.is_Ok() ==> is_readonly_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.log.unbounded_log_instance@) && result.get_Ok_0().1.WF(&self.replicas.spec_index(tkn.replica_id_spec() as int)),
    //     result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            // get the replica/node, execute it with the log and provide the thread id.
            Ok((&self.replicas[replica_id]).execute(&self.log, op, tkn, ticket))
        } else {
            Err((tkn, ticket))
        }
    }
}

} // verus!
