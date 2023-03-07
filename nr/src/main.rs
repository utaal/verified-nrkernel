// the verus dependencies
#[macro_use]
mod pervasive;
use pervasive::prelude::*;

use pervasive::map::Map;
use pervasive::vec::Vec;

mod spec;
// mod exec;

use spec::types::*;
use spec::unbounded_log::UnboundedLog;
use spec::cyclicbuffer::CyclicBuffer;

use pervasive::atomic_ghost::*;

use crate::pervasive::struct_with_invariants;




/// a simpe cache padding for the struct fields
#[repr(align(128))]
pub struct CachePadded<T>(T);


pub const MAX_REPLICAS_PER_LOG: usize = 16;
pub const DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;





verus!{


// struct_with_invariants!{
//     #[repr(align(128))]
//     pub struct LogEntry<T> {
//         /// The operation that this entry represents.
//         operation: Option<T>,

//         /// Identifies the replica that issued the above operation.
//         pub(crate) replica: usize,

//         /// Indicates whether this entry represents a valid operation when on the log.
//         alive: <AtomicU64<_, CyclicBuffer::alive_bits, _>>,

//         #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
//     }

//     pub closed spec fn wf(&self) -> bool {
//         invariant on alive with (cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits) {
//             g@ === CyclicBuffer::token![ cyclic_buffer_instance => version_upper_bound => v as nat ]
//         }
//     }
// }



struct_with_invariants!{
    #[repr(align(128))]
    // rename to log?
    struct NrLog {
        // /// The actual log, a slice of entries.
        // pub(crate) slog: Box<[Cell<Entry<T, M>>]>,

        /// Completed tail maintains an index <= tail that points to a log entry after which there
        /// are no completed operations across all replicas registered against this log.
        version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound, _>>,

        /// Logical index into the above slice at which the log starts.
        head: CachePadded<AtomicU64<_, CyclicBuffer::head, _>>,

        /// Logical index into the above slice at which the log ends. New appends go here.
        tail: CachePadded<AtomicU64<_, CyclicBuffer::tail, _>>,

        // globalTail: CachePadded<Atomic<u64, GlobalTailTokens>>,
        local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions, CyclicBuffer::local_versions), _>>>,  // NodeInfo is padded

        // buffer: lseq<LogEntry>,
        // bufferContents: GhostAtomic<CBContents>, // !ghost


        // #[verifier::proof] local_reads: Map<ReqId, ReadonlyState>,  // ghost

        #[verifier::proof] local_reads: UnboundedLog::local_reads,

        // ghost cb_loc_s: nat
        // ...

        #[verifier::proof] unbounded_log_instance: UnboundedLog::Instance,
        #[verifier::proof] cyclic_buffer_instance: CyclicBuffer::Instance,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            // TODO from example, replace
            // TODO &&& self.instance.backing_cells().len() == self.buffer@.len()
            // TODO &&& (forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
            // TODO     self.instance.backing_cells().index(i) ===
            // TODO         self.buffer@.index(i).id())
            true
        }

        invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound) {
            g@ === UnboundedLog::token![ unbounded_log_instance => version_upper_bound => v as nat ]
        }

        invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head) {
            g@ === CyclicBuffer::token![ cyclic_buffer_instance => head => v as nat ]
        }

        invariant on tail with (cyclic_buffer_instance) specifically (self.tail.0) is (v: u64, g: CyclicBuffer::tail) {
            g@ === CyclicBuffer::token![ cyclic_buffer_instance => tail => v as nat ]
        }


        invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
            forall |i: int|
            where (0 <= i < self.local_versions@.len())
            specifically (self.local_versions@[i].0)
            is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_versions)) {

            &&& g.0@ === UnboundedLog::token![ unbounded_log_instance => local_versions => i as nat => v as nat ]
            &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance => local_versions => i as nat => v as nat ]
        }

        // invariant on local_reads with (unbounded_log_instance)
        //     forall |i: int|
        //     where (0 <= i < self.local_reads@.contains())
        //     is (v: Map<ReqId, ReadonlyState>, g: UnboundedLog::local_reads) {
        //     g@ === UnboundedLog::token![ unbounded_log_instance => local_reads => v ]
        // }

    }
}


// CachePadded<
//     pervasive::atomic_ghost::AtomicU64<
//         (spec::unbounded_log::UnboundedLog::Instance, spec::cyclicbuffer::CyclicBuffer::Instance, builtin::int),
//         (spec::unbounded_log::UnboundedLog::local_versions, spec::cyclicbuffer::CyclicBuffer::local_versions),
//         InvariantPredicate_auto_NrLog_local_versions
//     >
// >
use pervasive::cell::*;
impl NrLog {

    /// checks whether the version of the local replica has advanced enough to perform read operations
    ///
    /// This basically corresponds to the transition `readonly_read_to_read` in the unbounded log.
    ///
    // https://github.com/vmware/node-replication/blob/57075c3ddaaab1098d3ec0c2b7d01cb3b57e1ac7/node-replication/src/log.rs#L525
    pub fn is_replica_synced_for_reads(&mut self, node_id: usize, version_upper_bound: u64) -> bool

        requires
          old(self).wf(),
        //   old(self).unbounded_log_instance.local_reads[]
        // TODO: more stuff here
    {
        // obtain the local version
        let local_version = &self.local_versions.index(node_id).0;

        // #[verifier::proof]
        let rid : u64 = 0; // XXX: where to get that from?



        #[verifier::proof]
        let new_local_reads: Option<UnboundedLog::local_reads>;

        //  self.ltails[idx.0 - 1].load(Ordering::Relaxed) >= ctail
        let res = atomic_with_ghost!(
            local_version => load();
            returning res;
            ghost g => {
                new_local_reads = if res >= version_upper_bound {
                    /// XXX: is that the right thing to do with local_reads, or do they need to be obtained differently?
                    #[verifier::proof] let new_local_reads = self.unbounded_log_instance.readonly_ready_to_read(rid as nat, node_id as NodeId, &g.0, self.local_reads);
                    Option::Some(new_local_reads)
                } else {
                    Option::None
                };

                // assert(ret as nat == g.1.index(node_id));
            }
        );

        if let Some(lrds) = new_local_reads {
            // the change has happened

            self.local_reads = lrds;

        } else {
            // no change at all
        }

        res >= version_upper_bound
    }
}

} // verus!

pub fn main() {}
