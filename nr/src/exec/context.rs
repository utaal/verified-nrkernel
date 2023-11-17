#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{
    prelude::*,
    cell::{PCell, PointsTo, CellId},
    atomic_ghost::AtomicU64,
    atomic_with_ghost,
};

use crate::Dispatch;

// constants
use crate::constants::{MAX_THREADS_PER_REPLICA};

// spec import
use crate::spec::unbounded_log::UnboundedLog;
use crate::spec::flat_combiner::FlatCombiner;

// exec imports
use crate::exec::CachePadded;
use crate::exec::replica::{ReplicaToken, ReplicaId};

verus! {


////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Token
////////////////////////////////////////////////////////////////////////////////////////////////////


/// A (monotoically increasing) number that uniquely identifies a thread that's
/// registered with the replica.
pub type ThreadId = u32;


/// the thread token identifies a thread of a given replica
///
///  - Dafny: linear datatype ThreadOwnedContext
pub struct ThreadToken<DT: Dispatch> {
    /// the replica id this thread uses
    pub /* REVIEW: (crate) */ rid: ReplicaToken,
    /// identifies the thread within the replica
    pub /* REVIEW: (crate) */ tid: ThreadId,
    /// the flat combiner client of the thread
    pub fc_client: Tracked<FlatCombiner::clients>,
    /// the permission to access the thread's operation batch
    pub batch_perm: Tracked<PointsTo<PendingOperation<DT>>>,
}

impl<DT: Dispatch> ThreadToken<DT> {
    pub open spec fn wf(&self) -> bool
    {
        &&& self.rid.wf()
        &&& self.fc_client@@.value.is_Idle()
        &&& (self.tid as nat) < MAX_THREADS_PER_REPLICA
        // &&& self.fc_client@@.instance == fc_inst
        &&& self.batch_perm@@.value.is_None()
        &&& self.fc_client@@.key == self.tid as nat
    }

    pub fn thread_id(&self) -> (result: ThreadId)
        ensures result as nat == self.thread_id_spec()
    {
        self.tid
    }

    pub open spec fn thread_id_spec(&self) -> nat {
        self.tid as nat
    }

    pub const fn replica_id(&self) -> (result: ReplicaId)
        ensures result as nat == self.replica_id_spec()
    {
        self.rid.id()
    }

    pub open spec fn replica_token(&self) -> ReplicaToken {
        self.rid
    }

    pub open spec fn replica_id_spec(&self) -> nat {
        self.rid.id_spec()
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Pending Operation
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Data for a pending operation.
///
///  - Dafny: datatype OpResponse
///  - Rust:  pub struct PendingOperation<T, R, M> {
///
/// In Dafny those data types are not options, but in Rust they are
pub struct PendingOperation<DT: Dispatch> {
    /// the operation that is being executed
    pub/*REVIEW: (crate)*/ op: DT::WriteOperation,
    /// the response of the operation
    pub/*REVIEW: (crate)*/ resp: Option<DT::Response>,
}

impl<DT: Dispatch> PendingOperation<DT> {
    pub fn new(op: DT::WriteOperation) -> (res: Self)
        ensures res.op == op
    {
        PendingOperation {
            op,
            resp: None,
        }
    }

    pub fn set_result(&mut self, resp: DT::Response) {
        self.resp = Some(resp);
    }

    // pub fn to_result(self) -> DT::Response {
    //     self.resp.get_Some_0()
    // }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Context
////////////////////////////////////////////////////////////////////////////////////////////////////



struct_with_invariants!{
/// Contains state of a particular thread context within NR w.r.g. to outstanding operations.
///
///  - Dafny: linear datatype Context = Context(
///  - Rust:  pub(crate) struct Context<T, R, M>
///
/// Note, in contrast to the Rust version, we just have a single outstanding operation
#[repr(align(128))]
pub struct Context<DT: Dispatch> {
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    ///
    /// This is protected by the `atomic` field.
    ///
    ///  - Dafny: linear cell: CachePadded<Cell<OpResponse>>
    ///  - Rust:  pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],
    pub/*REVIEW: (crate)*/ batch: CachePadded<PCell<PendingOperation<DT>>>,

    /// The number of operations in this context, (just 0 or 1)
    ///
    ///  - Dafny: linear atomic: CachePadded<Atomic<uint64, ContextGhost>>,
    ///  - Rust:  N/A
    pub/*REVIEW: (crate)*/ atomic: CachePadded<AtomicU64<_, ContextGhost<DT>, _>>,

    /// ghost: identifier of the thread
    pub thread_id_g: Ghost<nat>,

    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
}

pub open spec fn wf(&self, thread_idx: nat) -> bool {
    predicate {
        self.thread_id_g@ == thread_idx
    }
    invariant on atomic with (flat_combiner_instance, unbounded_log_instance, batch, thread_id_g) specifically (self.atomic.0) is (v: u64, g: ContextGhost<DT>) {
        &&& g.inv(v, thread_id_g@, batch.0, flat_combiner_instance@, unbounded_log_instance@)
    }
}} // struct_with_invariants!

impl<DT: Dispatch> Context<DT> {

    pub fn new(thread_id: usize, slot: Tracked<FlatCombiner::slots>, flat_combiner_instance: Tracked<FlatCombiner::Instance>, unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>)
        -> (res: (Context<DT>, Tracked<PointsTo<PendingOperation<DT>>>))
        requires
            slot@@.value.is_Empty(),
            slot@@.instance == flat_combiner_instance,
            slot@@.key == thread_id as nat
        ensures
            res.0.wf(thread_id as nat),
            res.0.flat_combiner_instance == flat_combiner_instance,
            res.0.unbounded_log_instance == unbounded_log_instance,
            res.1@@.value.is_None()
        {
        let ghost mut thread_id_g;
        proof {
            thread_id_g = thread_id as nat;
        }

        // create the storage for storing the update operation
        let (batch, batch_perms) = PCell::empty();
        let batch = CachePadded(batch);

        // create the atomic with the ghost context
        let tracked context_ghost = ContextGhost {
            batch_perms: None,
            slots: slot.get(),
            update: Option::None,
        };
        let atomic = AtomicU64::new(Ghost((flat_combiner_instance, unbounded_log_instance, batch, Ghost(thread_id_g))), 0, Tracked(context_ghost));

        // Assemble the context, return with the permissions
        (Context {
            batch: batch,
            atomic: CachePadded(atomic),
            thread_id_g: Ghost(thread_id_g),
            flat_combiner_instance,
            unbounded_log_instance
        }, batch_perms)
    }

    /// Enqueues an operation onto this context's batch of pending operations.
    ///
    /// This is invoked by the thread that want's to execute an operation
    ///
    /// Note, enqueue is a bit a misnomer. We just have one operation per thread
    pub fn enqueue_op(&self, op: DT::WriteOperation, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
        -> (res: (bool, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            context_ghost@.enqueue_op_pre(self.thread_id_g@, op, self.batch.0.id(), self.flat_combiner_instance@, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.enqueue_op_post(context_ghost@),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost { batch_perms: batch_perms, local_updates: local_updates, fc_clients: mut fc_clients } = context_ghost.get();

        let tracked mut batch_perms = batch_perms.tracked_unwrap();
        let tracked local_updates = local_updates.tracked_unwrap();

        // put the operation there, updates the permissions so we can store them in the GhostContext
        self.batch.0.put(Tracked(&mut batch_perms), PendingOperation::new(op));

        let tracked send_request_result;
        let res = atomic_with_ghost!(
            &self.atomic.0 => store(1);
            update prev->next;
            ghost g => {
                let ghost tid = fc_clients.view().key;
                let ghost rid = local_updates.view().key;

                self.flat_combiner_instance.borrow().pre_send_request(tid, &fc_clients, &g.slots);
                send_request_result = self.flat_combiner_instance.borrow().send_request(tid, rid, fc_clients, g.slots);
                fc_clients = send_request_result.0.get();

                g.slots = send_request_result.1.get();
                g.batch_perms = Some(batch_perms);
                g.update = Some(local_updates);

                assert(g.inv(1, tid, self.batch.0, self.flat_combiner_instance.view(), self.unbounded_log_instance.view()))
            }
        );

        let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms: None, local_updates: None, fc_clients };
        (true, Tracked(new_context_ghost))
    }


    /// Returns a single response if available. Otherwise, returns None.
    ///
    /// this is invoked by the thread that has enqueued the operation before
    pub fn dequeue_response(&self, context_ghost: Tracked<FCClientRequestResponseGhost<DT>>)
        -> (res: (Option<DT::Response>, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            context_ghost@.dequeue_resp_pre(self.thread_id_g@, self.flat_combiner_instance@),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, res.0, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost { batch_perms: mut batch_perms, local_updates: mut local_updates, fc_clients: mut fc_clients } = context_ghost.get();

        let tracked recv_response_result;
        let res = atomic_with_ghost!(
            &self.atomic.0 => load();
            returning res;
            ghost g => {
                if res == 0 {
                    batch_perms = g.batch_perms;
                    local_updates = g.update;

                    let tid = fc_clients.view().key;
                    let rid = fc_clients.view().value.get_Waiting_0();
                    self.flat_combiner_instance.borrow().pre_recv_response(tid, &fc_clients, &g.slots);
                    recv_response_result = self.flat_combiner_instance.borrow().recv_response(tid, rid, fc_clients, g.slots);
                    fc_clients = recv_response_result.0.get();

                    g.slots = recv_response_result.1.get();
                    g.batch_perms = None;
                    g.update = None;
                }
            }
        );

        if res == 0 {
            let tracked mut batch_perms = batch_perms.tracked_unwrap();
            let op = self.batch.0.take(Tracked(&mut batch_perms));
            let resp = op.resp.unwrap();
            let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms: Some(batch_perms), local_updates, fc_clients };
            (Some(resp), Tracked(new_context_ghost))
        } else {
            let tracked new_context_ghost = FCClientRequestResponseGhost { batch_perms, local_updates, fc_clients };
            (None, Tracked(new_context_ghost))
        }
    }


    /// Enqueues a response onto this context. This is invoked by the combiner
    /// after it has executed operations (obtained through a call to ops()) against the
    /// replica this thread is registered against.
    pub fn enqueue_response(&self, resp: DT::Response) -> bool
        requires
            self.wf(self.thread_id_g@)
            // self.atomic != 0
    {
        // let tracked token : Option<Tracked<PointsTo<PendingOperation>>>;
        // let res = atomic_with_ghost!(
        //     &self.atomic.0 => load();
        //     returning res;
        //     ghost g => {
        //         if res == 1 {
        //             // store the operatin in the cell
        //             token =  Some(g.batch_perms);
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



////////////////////////////////////////////////////////////////////////////////////////////////////
// Ghost Context
////////////////////////////////////////////////////////////////////////////////////////////////////

struct_with_invariants!{
/// The ghost context for a thread carying permissions and tracking the state of the update operation
///
///  - Dafny:   glinear datatype ContextGhost = ContextGhost(
pub tracked struct ContextGhost<DT: Dispatch> {
    /// Token to access the batch cell in Context
    ///
    ///  - Dafny: glinear contents: glOption<CellContents<OpResponse>>,
    pub batch_perms: Option<PointsTo<PendingOperation<DT>>>,

    /// The flat combiner slot.
    ///
    ///  - Dafny: glinear fc: FCSlot,
    pub slots: FlatCombiner::slots,

    /// tracks the update operation
    ///
    ///  - Dafny: glinear update: glOption<Update>
    pub update: Option<UnboundedLog::local_updates<DT>>
}

//  - Dafny: predicate inv(v: uint64, i: nat, cell: Cell<OpResponse>, fc_loc_s: nat)
pub open spec fn inv(&self, v: u64, tid: nat, cell: PCell<PendingOperation<DT>>, fc: FlatCombiner::Instance, inst: UnboundedLog::Instance<DT>) -> bool {
    predicate {
        &&& self.slots@.key == tid
        &&& self.slots@.instance == fc

        &&& ((v == 0) || (v == 1))
        &&& (v == 0 ==> self.slots@.value.is_Empty() || self.slots@.value.is_Response())
        &&& (v == 1 ==> self.slots@.value.is_Request() || self.slots@.value.is_InProgress())

        &&& (self.slots@.value.is_Empty() ==> {
            &&& self.update.is_None()
            &&& self.batch_perms.is_None()
        })

        &&& (self.slots@.value.is_Request() ==> {
            &&& self.update.is_Some()
            &&& self.update.get_Some_0()@.value.is_Init()
            &&& self.update.get_Some_0()@.key == self.slots@.value.get_ReqId()
            &&& self.update.get_Some_0()@.instance == inst

            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_Some()
            &&& self.batch_perms.get_Some_0()@.pcell == cell.id()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().op == self.update.get_Some_0()@.value.get_Init_op()
        })

        &&& (self.slots@.value.is_InProgress() ==> {
            &&& self.update.is_None()
            &&& self.batch_perms.is_None()
        })

        &&& (self.slots@.value.is_Response() ==> {
            &&& self.update.is_Some()
            &&& self.update.get_Some_0()@.value.is_Done()
            &&& self.update.get_Some_0()@.key == self.slots@.value.get_ReqId()
            &&& self.update.get_Some_0()@.instance == inst

            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_Some()
            &&& self.batch_perms.get_Some_0()@.pcell == cell.id()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().resp.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.get_Some_0().resp.get_Some_0() == self.update.get_Some_0()@.value.get_Done_ret()
        })
    }
}
} // struct_with_invariants! ContextGhost


/// Request Enqueue/Dequeue ghost state
pub tracked struct FCClientRequestResponseGhost<DT: Dispatch> {
    pub tracked batch_perms: Option<PointsTo<PendingOperation<DT>>>,
    pub tracked local_updates: Option<UnboundedLog::local_updates<DT>>,
    pub tracked fc_clients: FlatCombiner::clients
}

impl<DT: Dispatch> FCClientRequestResponseGhost<DT> {
    pub open spec fn enqueue_op_pre(&self, tid: nat, op: DT::WriteOperation, batch_cell: CellId, fc_inst: FlatCombiner::Instance, inst: UnboundedLog::Instance<DT>) -> bool {
        &&& self.local_updates.is_Some()
        &&& self.local_updates.get_Some_0()@.instance == inst
        &&& self.local_updates.get_Some_0()@.value.is_Init()
        &&& self.local_updates.get_Some_0()@.value.get_Init_op() == op

        &&& self.batch_perms.is_Some()
        &&& self.batch_perms.get_Some_0()@.pcell == batch_cell
        &&& self.batch_perms.get_Some_0()@.value.is_None()

        &&& self.fc_clients@.instance == fc_inst
        &&& self.fc_clients@.key == tid
        &&& self.fc_clients@.value.is_Idle()
    }

    pub open spec fn enqueue_op_post(&self, pre: FCClientRequestResponseGhost<DT>) -> bool
        recommends pre.local_updates.is_Some()
    {
        &&& self.fc_clients@.value.is_Waiting()
        &&& self.fc_clients@.value.get_Waiting_0() == pre.local_updates.get_Some_0()@.key
        &&& self.fc_clients@.instance == pre.fc_clients@.instance
        &&& self.fc_clients@.key == pre.fc_clients@.key

        &&& self.batch_perms.is_None()
        &&& self.local_updates.is_None()
    }

    pub open spec fn dequeue_resp_pre(&self, tid: nat, fc_inst: FlatCombiner::Instance) -> bool {
        &&& self.fc_clients@.key == tid
        &&& self.fc_clients@.instance == fc_inst
        &&& self.fc_clients@.value.is_Waiting()

        &&& self.batch_perms.is_None()
        &&& self.local_updates.is_None()
    }

    pub open spec fn dequeue_resp_post(&self, pre: FCClientRequestResponseGhost<DT>, ret: Option<DT::Response>, inst: UnboundedLog::Instance<DT>) -> bool {
        &&& ret.is_Some() ==> {
            &&& self.batch_perms.is_Some()
            &&& self.batch_perms.get_Some_0()@.value.is_None()

            &&& self.local_updates.is_Some()
            &&& self.local_updates.get_Some_0()@.instance == inst
            &&& self.local_updates.get_Some_0()@.value.is_Done()
            &&& self.local_updates.get_Some_0()@.key == pre.fc_clients@.value.get_Waiting_0()
            &&& self.local_updates.get_Some_0()@.value.get_Done_ret() == ret.get_Some_0()

            &&& self.fc_clients@.instance == pre.fc_clients@.instance
            &&& self.fc_clients@.key == pre.fc_clients@.key
            &&& self.fc_clients@.value.is_Idle()
        }
        &&& ret.is_None() ==> {
            &&& self == pre
        }
    }
}

} // verus!
