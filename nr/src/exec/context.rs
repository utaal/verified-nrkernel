use builtin_macros::verus_old_todo_no_ghost_blocks;


use crate::pervasive::prelude::*;
use crate::pervasive::cell::{PCell, PointsTo};
use crate::pervasive::map::Map;
use crate::pervasive::option::Option;
use crate::pervasive::vec::Vec;
use crate::pervasive::atomic_ghost::*;
use crate::pervasive::struct_with_invariants;

use crate::spec::cyclicbuffer::CyclicBuffer;
use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::types::*;
use crate::spec::unbounded_log::UnboundedLog;

use super::cachepadded::CachePadded;
use super::ReplicaId;
use super::replica::ReplicaToken;

verus! {


/// the thread token identifies a thread of a given replica
pub struct ThreadToken {
    /// the replica id this thread uses
    pub(crate) rid: ReplicaId,
    /// identifies the thread within the replica
    pub(crate) tid: ReplicaToken,
}

pub struct LogToken {
    id: usize
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
    pub(crate) op: Option<UpdateOp>,
    /// the response of the operation
    pub(crate) resp: Option<ReturnType>,
}

impl PendingOperation {
    // pub fn new(op: UpdateOp) -> Self {
    //     Self {
    //         op: Some(op),
    //         resp: None,
    //     }
    // }

    pub fn set_result(&mut self, resp: ReturnType) {
        self.resp = Some(resp);
    }

    // pub fn to_result(self) -> ReturnType {
    //     self.resp.get_Some_0()
    // }
}

struct_with_invariants!{
pub struct ContextGhost {
    /// Token to access the batch cell in Context
    ///
    ///  - Dafny: glinear contents: glOption<CellContents<OpResponse>>,
    pub batch_token: Tracked<PointsTo<PendingOperation>>,

    // The flat combiner
    // fc: FCSlot
    pub flat_combiner_slots: FlatCombiner::slots,

    // update: UpdateTicket?
    pub update: Tracked<UnboundedLog::local_updates>
}

pub closed spec fn inv(&self, v: u64, i: nat, cell: PCell<PendingOperation>) -> bool {

}
} // struct_with_invariants! ContextGhost


struct_with_invariants!{
/// Contains state of a particular thread w.r.g. to outstanding operations.
///
///  - Dafny: linear datatype Context
///  - Rust:  pub(crate) struct Context<T, R, M>
///
/// Note, in contrast to the Rust version, we just have a single outstanding operation
#[repr(align(128))]
pub struct Context {
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    ///
    ///  - Dafny: linear cell: CachePadded<Cell<OpResponse>>
    ///  - Rust:  pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],
    batch: CachePadded<PCell<PendingOperation>>,

    /// maybe some kind of lock?
    ///  - Dafny: linear atomic: CachePadded<Atomic<uint64, ContextGhost>>,
    ///  - Rust:  N/A
    atomic: CachePadded<AtomicU64<_, ContextGhost, _>>,

    /// ghost
    pub thread_id_g: Tracked<ThreadToken>,
}

pub closed spec fn wf(&self) -> bool {
    predicate {
        true
    }

    invariant on atomic specifically (self.atomic.0) is (v: u64, g: ContextGhost) {
      // (forall v, g :: atomic_inv(atomic.inner, v, g) <==> g.inv(v, i, cell.inner, fc_loc))
      // atomic.atomic_inv() <==> g.inv(v, i, self.batch)
      &&& (v == 0) <==> g.batch_token@@.value.is_None()
    }
}} // struct_with_invariants!

impl Context {

    pub open spec fn get_thread_id(&self) -> nat {
        self.thread_id_g@.tid as nat
    }

    /// Enqueues an operation onto this context's batch of pending operations.
    pub fn enqueue_op(&self, op: UpdateOp, tracked update: Tracked<UnboundedLog::local_updates>)
        -> bool
        requires self.wf()
    {
        // enqueue is a bit a misnomer here, we actually only have one slot in the batch for now.

        // let tracked token : Option<Tracked<PointsTo<PendingOperation>>>;
        // let res = atomic_with_ghost!(
        //     &self.atomic.0 => compare_exchange(0, 1);
        //     update prev->next;
        //     ghost g => {
        //         if prev == 0 {
        //             // store the operatin in the cell
        //             token =  Some(g.batch_token);
        //         } else {
        //             token = None;
        //         }
        //     }
        // );

        // if res.is_Ok() {
        //     if res.get_Ok_0() == 0 {
        //         let tracked token = token.get_Some_0();
        //         let pending_op = PendingOperation {
        //             op: Some(op),
        //             resp: None,
        //         };

        //         // HERE:
        //         // self.batch.0.put(&mut token, pending_op);
        //         true
        //     } else {
        //         false
        //     }
        // } else {
        //     false
        // }
        false
    }

    /// Enqueues a response onto this context. This is invoked by the combiner
    /// after it has executed operations (obtained through a call to ops()) against the
    /// replica this thread is registered against.
    pub fn enqueue_response(&self, resp: ReturnType) -> bool
        requires
            self.wf(),
            // self.atomic != 0
    {
        // let tracked token : Option<Tracked<PointsTo<PendingOperation>>>;
        // let res = atomic_with_ghost!(
        //     &self.atomic.0 => load();
        //     returning res;
        //     ghost g => {
        //         if res == 1 {
        //             // store the operatin in the cell
        //             token =  Some(g.batch_token);
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

    /// Returns a single response if available. Otherwise, returns None.
    pub fn get_result(&self) -> Option<ReturnType>
        requires self.wf()
    {
        // let tracked token : Option<Tracked<PointsTo<PendingOperation>>>;
        // // let res = atomic_with_ghost!(
        // //     &self.atomic.0 => compare_exchange(1, 0);
        // //     update prev->next;
        // //     ghost g => {
        // //         if prev == 1 {
        // //             // store the operatin in the cell
        // //             token =  Some(g.batch_token);
        // //         } else {
        // //             token = None;
        // //         }
        // //     }
        // // );

        // if res.get_Ok_0() != 0 {
        //     // let pending_op = self.batch.0.take(token.get_Some_0());
        //     // let response = pending_op.resp.get_Some_0();
        //     // Some(response)
        //     None
        // } else {
        //     None
        // }
        None
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

}