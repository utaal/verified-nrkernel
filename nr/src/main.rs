// the verus dependencies
#[macro_use]
mod pervasive;
use pervasive::prelude::*;

use pervasive::vec::Vec;

mod spec;

use spec::types::*;
use spec::unbounded_log::UnboundedLog;
use spec::cyclicbuffer::CyclicBuffer;

use pervasive::atomic_ghost::*;

use crate::pervasive::struct_with_invariants;

#[repr(align(128))]
pub struct CachePadded<T>(T);

struct_with_invariants!{
    struct NR {
        version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound, _>>,
        head: CachePadded<AtomicU64<_, CyclicBuffer::head, _>>,
        // globalTail: CachePadded<Atomic<u64, GlobalTailTokens>>,
        node_info: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions, CyclicBuffer::local_heads), _>>>,  // NodeInfo is padded

        // buffer: lseq<BufferEntry>,
        // bufferContents: GhostAtomic<CBContents>, // !ghost

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

        invariant on node_info with (unbounded_log_instance, cyclic_buffer_instance)
            forall |i: int|
            where (0 <= i < self.node_info@.len())
            specifically (self.node_info@[i].0)
            is (v: u64, g: (UnboundedLog::local_versions, CyclicBuffer::local_heads)) {
        
            &&& g.0@ === UnboundedLog::token![ unbounded_log_instance => local_versions => i as nat => v as nat ]
            &&& g.1@ === CyclicBuffer::token![ cyclic_buffer_instance => local_heads => i as nat => v as nat ]
        }
    }
}

pub fn main() {}
