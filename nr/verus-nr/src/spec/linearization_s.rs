// The Linearization Proof


#[allow(unused_imports)]
use builtin::*;
use vstd::*;
use vstd::seq::*;
use vstd::prelude::*;
use state_machines_macros::state_machine;

use vstd::prelude::is_variant;

use crate::spec::simple_log::SimpleLog;
use crate::ReqId;
use crate::Dispatch;

verus! {

/// A lable representing whether we are performing an internal operation,
/// or whether the transition is the start or end of a outer request
#[is_variant]
pub enum AsyncLabel<DT: Dispatch> {
    Internal,
    Start(ReqId, InputOperation<DT>),
    End(ReqId, OutputOperation<DT>),
}

/// function tying the SimpleLog transition with the async lable
///
/// XXX: This should come directly from the state machine macro!
pub open spec fn async_op_matches<DT: Dispatch>(pre: SimpleLog::State<DT>, post:SimpleLog::State<DT>, op: AsyncLabel<DT>) -> bool
    recommends exists |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(pre, post, step)
{
    let step = choose |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(pre, post, step);
    match step {
         SimpleLog::Step::readonly_start(rid, rd_op)        => op == AsyncLabel::Start(rid, InputOperation::<DT>::Read(rd_op)),
         SimpleLog::Step::readonly_read_version(_rid)       => op.is_Internal(),
         SimpleLog::Step::readonly_finish(rid, _idx, resp)  => op == AsyncLabel::End(rid, OutputOperation::<DT>::Read(resp)),
         SimpleLog::Step::update_start(rid, wr_op)          => op == AsyncLabel::Start(rid, InputOperation::<DT>::Write(wr_op)),
         SimpleLog::Step::update_add_op_to_log(_rid)        => op.is_Internal(),
         SimpleLog::Step::update_incr_version(_idx)         => op.is_Internal(),
         SimpleLog::Step::update_finish(rid, resp)          => op == AsyncLabel::End(rid, OutputOperation::<DT>::Read(resp)),
         SimpleLog::Step::no_op()                           => op.is_Internal(),
         SimpleLog::Step::dummy_to_use_type_params(_st)     => op.is_Internal(),
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
//                       State Machine For A Single-Step Data Structure                           //
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Signifies a request that may be a read or a write operation
#[is_variant]
pub enum InputOperation<DT: Dispatch> {
    Read(DT::ReadOperation),
    Write(DT::WriteOperation),
}

/// Signifies a response that may be the result to a read or write operation
#[is_variant]
pub enum OutputOperation<DT: Dispatch> {
    Read(DT::Response),
    Write(DT::Response),
}


state_machine!{ AsynchronousSingleton<DT: Dispatch> {
    fields {
        pub state: DT::View,
        pub reqs: Map<ReqId, InputOperation<DT>>,
        pub resps: Map<ReqId, OutputOperation<DT>>,
    }

    //pub type Label<DT> = AsyncLabel<DT>;

    init!{
        initialize() {
            init state = DT::init_spec();
            init reqs = Map::empty();
            init resps = Map::empty();
        }
    }

    transition!{
        internal_next(rid: ReqId, input: InputOperation<DT>, output: OutputOperation<DT>) {
            require pre.reqs.dom().contains(rid);
            require pre.reqs[rid] == input;
            update reqs = pre.reqs.remove(rid);
            update resps = pre.resps.insert(rid, output);

            match input {
                InputOperation::Read(read_op) => {
                    require output === OutputOperation::Read(DT::dispatch_spec(pre.state, read_op));
                }
                InputOperation::Write(write_op) => {
                    let (next_state, out) = DT::dispatch_mut_spec(pre.state, write_op);
                    require output === OutputOperation::Write(out);
                    update state = next_state;
                }
            }
        }
    }

    transition!{
        no_op() { /* stutter step */ }
    }

    transition!{
        start(rid: ReqId, input: InputOperation<DT>) {
            require !pre.reqs.dom().contains(rid);
            update reqs = pre.reqs.insert(rid, input);
        }
    }

    transition!{
        end(rid: ReqId, output: OutputOperation<DT>) {
            require pre.resps.dom().contains(rid);
            require pre.resps[rid] == output;
            update resps = pre.resps.remove(rid);
        }
    }
}}

////////////////////////////////////////////////////////////////////////////////////////////////////
//                                AsynchronousSingleton Behavior                                  //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[is_variant]
pub enum AsynchronousSingletonBehavior<DT: Dispatch> {
    Stepped(AsynchronousSingleton::State<DT>, AsyncLabel<DT>, Box<AsynchronousSingletonBehavior<DT>>),
    Inited(AsynchronousSingleton::State<DT>),
}

impl<DT: Dispatch> AsynchronousSingletonBehavior<DT> {
    pub open spec fn get_last(self) -> AsynchronousSingleton::State<DT> {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => post,
            AsynchronousSingletonBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => {
                tail.wf() && AsynchronousSingleton::State::next(/* op, */ tail.get_last(), post)
            }
            AsynchronousSingletonBehavior::Inited(post) => {
                AsynchronousSingleton::State::init(post)
            }
        }
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
//                                   Simple Log Behavior                                          //
////////////////////////////////////////////////////////////////////////////////////////////////////

#[is_variant]
pub enum SimpleLogBehavior<DT: Dispatch> {
    Stepped(SimpleLog::State<DT>, AsyncLabel<DT>, Box<SimpleLogBehavior<DT>>),
    Inited(SimpleLog::State<DT>),
}

impl<DT: Dispatch> SimpleLogBehavior<DT> {
    pub open spec fn get_last(self) -> SimpleLog::State<DT> {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => post,
            SimpleLogBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => {
                tail.wf() && SimpleLog::State::next(/* op, */ tail.get_last(), post)
                && async_op_matches(tail.get_last(), post, op)
            }
            SimpleLogBehavior::Inited(post) => {
                SimpleLog::State::init(post)
            }
        }
    }
}

} // end verus!