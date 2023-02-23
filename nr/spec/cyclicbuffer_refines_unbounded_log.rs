// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use super::pervasive::map::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::seq::Seq;
use super::pervasive::seq_lib::*;
//use super::pervasive::set::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::arbitrary;

use state_machines_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use super::unbounded_log::{CombinerState, ReadonlyState, UnboundedLog, UpdateState};
#[allow(unused_imports)] // XXX: should not be needed!
use super::types::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::cyclicbuffer::{CyclicBuffer};
#[allow(unused_imports)] // XXX: should not be needed!
use super::utils::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Refinement Proof: Cyclicbuffer refines UnboundedLog
// ===================================================
//
////////////////////////////////////////////////////////////////////////////////////////////////////


verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interpretation Function
////////////////////////////////////////////////////////////////////////////////////////////////////

spec fn interp_log(log: Map<LogicalLogIdx, StoredType>) -> Map<LogIdx, LogEntry> {
    Map::new(|i: LogIdx| 0 <= i && log.contains_key(i as LogicalLogIdx), |i| log[i])
}

spec fn interp_replicas()



spec fn interp(s: CyclicBuffer::State) -> UnboundedLog::State {
    UnboundedLog::State {
        num_replicas = s.num_replicas;
        log = interp_log(s.log);
        global_tail = s.global_tail;
        replicas = Map::new(|n: NodeId| n < number_of_nodes, |n| NRState::init());
        local_versions = Map::new(|n: NodeId| n < number_of_nodes, |n| 0);
        version_upper_bound = 0;
        local_reads = Map::empty();
        local_updates = Map::empty();
        combiner = Map::new(|n: NodeId| n < number_of_nodes, |n| CombinerState::Ready);
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Refinement Proof
////////////////////////////////////////////////////////////////////////////////////////////////////

#[proof]
fn refinement_inv(vars: CyclicBuffer::State)
    requires vars.invariant()
    ensures interp(vars).invariant()
{
}

#[proof]
fn refinement_init(post: CyclicBuffer::State)
    requires
        post.invariant(),
        CyclicBuffer::State::init(post)
    ensures
        UnboundedLog::State::init(interp(post)),
{
    case_on_init!{ post, CyclicBuffer => {
        initialize(number_of_nodes) => {
            assert_maps_equal!(interp(post).readonly_reqs, Map::empty());
            assert_maps_equal!(interp(post).update_reqs, Map::empty());
            assert_maps_equal!(interp(post).update_resps, Map::empty());
            assert_seqs_equal!(interp(post).log, Seq::empty());
            UnboundedLog::show::initialize(interp(post));
        }
    }}

}


#[proof]
fn refinement_next(pre: CyclicBuffer::State, post: CyclicBuffer::State)
    requires
        pre.invariant(),
        post.invariant(),
        CyclicBuffer::State::next_strong(pre, post),
    ensures
        UnboundedLog::State::next(interp(pre), interp(post)),
{
    case_on_next_strong! {
        pre, post, CyclicBuffer => {
        }
    }
}