use builtin_macros::verus_old_todo_no_ghost_blocks;

use crate::spec::cyclicbuffer::*;
use crate::spec::types::*;
use crate::spec::unbounded_log::*;

use crate::pervasive::prelude::*;
use crate::pervasive::vec::Vec;

mod log;
mod cachepadded;
mod replica;
mod rwlock;
mod context;

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


pub use context::ThreadToken;
pub use replica::Replica;
pub use log::NrLog;


////////////////////////////////////////////////////////////////////////////////////////////////////
// The Public Interface
////////////////////////////////////////////////////////////////////////////////////////////////////

verus_old_todo_no_ghost_blocks! {


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
    // replicas: Vec<Box<Replica<DataStructureSpec, UpdateOp, ReturnType>>>,
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

} // verus_old_todo_no_ghost_blocks!