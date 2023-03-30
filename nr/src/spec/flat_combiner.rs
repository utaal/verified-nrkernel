// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::map::*;
use super::pervasive::option::Option;
use super::pervasive::seq::*;
// use super::pervasive::set::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::arbitrary;

use state_machines_macros::*;

use super::types::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::utils::*;

verus! {

/// represents the state of a client thread
#[is_variant]
pub enum ClientState {
    Idle,
    Waiting(ReqId),
}

/// represents the state of a request in the queue
#[is_variant]
pub enum SlotState {
    Empty,
    Request(ReqId),
    InProgress(ReqId),
    Response(ReqId),
}

impl SlotState {
    pub open spec fn get_ReqId(&self) -> ReqId {
        match self {
            SlotState::Empty => arbitrary(),
            SlotState::Request(reqid) => *reqid,
            SlotState::InProgress(reqid) => *reqid,
            SlotState::Response(reqid) => *reqid,
        }
    }
}

/// represents the combiner state
#[is_variant]
pub enum CombinerState {
    Collecting(Seq<Option<ReqId>>),
    Responding(Seq<Option<ReqId>>, nat),
}

impl CombinerState {
    pub open spec fn req_len(self) -> nat {
        match self {
            CombinerState::Collecting(reqs) => reqs.len(),
            CombinerState::Responding(reqs, _) => reqs.len(),
        }
    }

    pub open spec fn req_is_none(self, tid: nat) -> bool
        recommends 0 <= tid < self.req_len()
    {
        match self {
            CombinerState::Collecting(reqs) => reqs[tid as int].is_None(),
            CombinerState::Responding(reqs, _) => reqs[tid as int].is_None(),
        }
    }

    pub open spec fn req_is_some(self, tid: nat) -> bool
        recommends 0 <= tid < self.req_len()
    {
        match self {
            CombinerState::Collecting(reqs) => reqs[tid as int].is_Some(),
            CombinerState::Responding(reqs, _) => reqs[tid as int].is_Some(),
        }
    }
}


// The flat combiner state machine
tokenized_state_machine! {
FlatCombiner {
    fields {
        /// the number of threads
        #[sharding(constant)]
        pub num_threads: nat,

        /// clients of the replica
        #[sharding(map)]
        pub clients: Map<ThreadId, ClientState>,

        #[sharding(map)]
        pub slots: Map<ThreadId, SlotState>,

        #[sharding(variable)]
        pub combiner: CombinerState,
    }

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////

    #[invariant]
    pub fn inv_complete(&self) -> bool {
        // clients are complete
        &&& (forall |i| self.clients.contains_key(i) <==> i < self.num_threads)
        // slots are complete
        &&& (forall |i| self.slots.contains_key(i) <==> i < self.num_threads)
    }


    // && Complete(x)
    #[invariant]
    pub fn inv_client_slot_empty(&self) -> bool {
        forall |i:nat| #[trigger] self.clients.contains_key(i)
            ==>  (self.clients[i].is_Idle() <==> self.slots[i].is_Empty())
    }

    #[invariant]
    pub fn inv_client_reqids(&self) -> bool {
        forall |i:nat| #[trigger] self.clients.contains_key(i) && self.clients[i].is_Waiting()
            ==> self.clients[i].get_Waiting_0() == self.slots[i].get_ReqId()
    }

    #[invariant]
    pub fn inv_combiner_elements(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                elems.len() <= self.num_threads
            },
            CombinerState::Responding(elems, idx) => {
                &&& elems.len() == self.num_threads
                &&& idx <= elems.len()
            },
        }
    }

    pub open spec fn slot_in_progress(slots: Map<nat, SlotState>, tid: nat) -> bool
        recommends slots.contains_key(tid)
    {
        slots[tid].is_InProgress()
    }

    #[invariant]
    pub fn inv_combiner_slots_not_in_progress(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                // fff
                &&& (forall |i: nat| 0 <= i < elems.len() && elems[i as int].is_None()
                    ==> !(#[trigger] self.slots[i]).is_InProgress()) //Self::slot_in_progress(self.slots, i)))
                // everything above is not in progress
                &&& (forall |i: nat| elems.len() <= i < self.num_threads ==> !self.slots[i].is_InProgress())
            },
            CombinerState::Responding(elems, idx) => {
                &&& (forall |i: nat| 0 <= i < elems.len() && elems[i as int].is_None()
                    ==> !(#[trigger] self.slots[i]).is_InProgress()) //Self::slot_in_progress(self.slots, i)))
                &&& (forall |i: nat| 0 <= i < idx ==> !self.slots[i].is_InProgress())
            },
        }
    }

    #[invariant]
    pub fn inv_combiner_request_ids(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                forall |i:nat| (0 <= i < elems.len() && elems[i as int].is_Some())
                    ==> (#[trigger] self.slots[i]).is_InProgress() && self.slots[i].get_InProgress_0() == elems[i as int ].get_Some_0()
            },
            CombinerState::Responding(elems, idx) => {
                forall |i:nat| idx <= i < elems.len() && elems[i as int].is_Some()
                   ==> (#[trigger] self.slots[i]).is_InProgress() && self.slots[i].get_InProgress_0() == elems[i as int].get_Some_0()
            },
        }
    }




    ////////////////////////////////////////////////////////////////////////////////////////////
    // Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////


    init!{
        initialize(num_threads: nat) {
            init num_threads = num_threads;

            init clients = Map::new(|i:ThreadId| i < num_threads, |i| ClientState::Idle);
            init slots = Map::new(|i: nat| i < num_threads, |i| SlotState::Empty);

            init combiner = CombinerState::Collecting(Seq::empty());
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Combiner Collection of Requests
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// the combiner collects no request from the client
    transition!{
        combiner_collect_empty() {
            require(pre.combiner.is_Collecting());

            let tid = pre.combiner.get_Collecting_0().len();

            have slots >= [ tid => let (SlotState::Empty { .. } | SlotState::Response { .. }) ];

            update combiner = CombinerState::Collecting(pre.combiner.get_Collecting_0().push(Option::None));
        }
    }


    /// the combiner collects a request from the client
    transition!{
        combiner_collect_request() {
            require(pre.combiner.is_Collecting());

            let tid = pre.combiner.get_Collecting_0().len();

            remove slots -= [ tid => let SlotState::Request(rid) ];
            add    slots += [ tid => SlotState::InProgress(rid) ];

            update combiner = CombinerState::Collecting(pre.combiner.get_Collecting_0().push(Option::Some(rid)));
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Combiner Responding to Requests
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// combiner starts responding to requests
    transition!{
        combiner_responding_start() {
            require(pre.combiner.is_Collecting());
            require(pre.combiner.get_Collecting_0().len() == pre.num_threads);

            update combiner = CombinerState::Responding(pre.combiner.get_Collecting_0(), 0);
        }
    }

    /// combiner responds to an empty request
    transition!{
        combiner_responding_empty() {
            require(pre.combiner.is_Responding());
            let tid = pre.combiner.get_Responding_1();

            require(tid < pre.num_threads);
            require(pre.combiner.req_is_none(tid));

            update combiner = CombinerState::Responding(pre.combiner.get_Responding_0(), tid + 1);
        }
    }

    /// combiner responds to a request
    transition!{
        combiner_responding_result() {
            require(pre.combiner.is_Responding());

            let tid = pre.combiner.get_Responding_1();

            require(tid < pre.num_threads);
            require(!pre.combiner.req_is_none(tid));

            update combiner = CombinerState::Responding(pre.combiner.get_Responding_0(), tid + 1);
            remove slots -= [ tid => let r ];
            assert let SlotState::InProgress(rid) = r;
            add    slots += [ tid => SlotState::Response(rid) ];
        }
    }

    /// combiner is done responding to requests
    transition!{
        combiner_responding_done() {
            require(pre.combiner.is_Responding());
            require(pre.combiner.get_Responding_1() == pre.num_threads);

            update combiner = CombinerState::Collecting(Seq::empty());
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Sending
    ////////////////////////////////////////////////////////////////////////////////////////////


    transition!{
        send_request(tid: ThreadId, rid: ReqId) {
            remove clients -= [ tid => let ClientState::Idle ];
            add    clients += [ tid => ClientState::Waiting(rid) ];

            remove slots -= [ tid => let SlotState::Empty ];
            add    slots += [ tid => SlotState::Request(rid) ];
        }
    }


    transition!{
        recv_response(tid: ThreadId, rid: ReqId) {
            remove clients -= [ tid => ClientState::Waiting(rid) ];
            add    clients += [ tid => ClientState::Idle ];

            remove slots -= [ tid => SlotState::Response(rid) ];
            add    slots += [ tid => SlotState::Empty ];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////


    #[inductive(initialize)]
    fn initialize_inductive(post: Self, num_threads: nat) { }

    #[inductive(combiner_collect_empty)]
    fn combiner_collect_empty_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_collect_request)]
    fn combiner_collect_request_inductive(pre: Self, post: Self) {
        match post.combiner {
            CombinerState::Collecting(elems) => {
                let idx = pre.combiner.get_Collecting_0().len();
                assert(forall |i: nat| 0 <= i < idx
                    ==> Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));
            },
            _ => {}
        }
    }

    #[inductive(combiner_responding_start)]
    fn combiner_responding_start_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_responding_empty)]
    fn combiner_responding_empty_inductive(pre: Self, post: Self) {
        match post.combiner {
            CombinerState::Responding(elems, idx) => {
                assert(!Self::slot_in_progress(pre.slots, (idx - 1) as nat));
            },
            _ => {}
        }
    }

    #[inductive(combiner_responding_result)]
    fn combiner_responding_result_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_responding_done)]
    fn combiner_responding_done_inductive(pre: Self, post: Self) { }

    #[inductive(send_request)]
    fn send_request_inductive(pre: Self, post: Self, tid: ThreadId, rid: ReqId) {
        assert(Self::slot_in_progress(post.slots, tid) == Self::slot_in_progress(pre.slots, tid));
        assert(forall |i: nat| 0 <= i < post.num_threads
            ==> #[trigger] Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));

    }

    #[inductive(recv_response)]
    fn recv_response_inductive(pre: Self, post: Self, tid: ThreadId, rid: ReqId) {
        assert(Self::slot_in_progress(post.slots, tid) == Self::slot_in_progress(pre.slots, tid));
        assert(forall |i: nat| 0 <= i < post.num_threads
            ==> #[trigger] Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));
    }

}} // tokenized_state_machine! { FlatCombiner { ...

} // verus!
