#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{prelude::*, seq::Seq};

use crate::spec::types::ReqId;

verus! {

pub open spec fn rids_match(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
) -> bool
    decreases bools_end - bools_start,
    when 0 <= bools_start <= bools_end <= bools.len() && 0 <= rids_start <= rids_end <= rids.len()
{
    if bools_end == bools_start {
        rids_end == rids_start
    } else {
        if bools[bools_end - 1].is_Some() {
            &&& rids_end > rids_start
            &&& rids[rids_end - 1] == bools[bools_end - 1].get_Some_0()
            &&& rids_match(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                (rids_end - 1) as nat,
            )
        } else {
            rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end)
        }
    }
}

pub proof fn rids_match_add_none(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        rids_match(bools.push(Option::None), rids, bools_start, bools_end, rids_start, rids_end),
    decreases bools_end - bools_start,
{
    let bools_new = bools.push(Option::None);
    if bools_end == bools_start {
        assert(rids_match(bools_new, rids, bools_start, bools_end, rids_start, rids_end));
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_add_none(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                (rids_end - 1) as nat,
            );
        } else {
            rids_match_add_none(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                rids_end,
            );
        }
    }
}

pub proof fn rids_match_add_rid(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
    rid: ReqId,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        rids_match(
            bools.push(Option::Some(rid)),
            rids.push(rid),
            bools_start,
            bools_end,
            rids_start,
            rids_end,
        ),
    decreases bools_end - bools_start,
{
    let bools_new = bools.push(Option::Some(rid));
    let rids_new = rids.push(rid);
    if bools_end == bools_start {
        assert(rids_match(bools_new, rids_new, bools_start, bools_end, rids_start, rids_end));
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_add_rid(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                (rids_end - 1) as nat,
                rid,
            );
        } else {
            rids_match_add_rid(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                rids_end,
                rid,
            );
        }
    }
}

pub proof fn rids_match_pop(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        bools_end == bools_start ==> {
            rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
        },
        bools_end > bools_start ==> {
            &&& bools[bools_start as int].is_Some() ==> {
                &&& rids_start < rids_end
                &&& rids[rids_start as int] == bools[bools_start as int].get_Some_0()
                &&& rids_match(
                    bools,
                    rids,
                    (bools_start + 1) as nat,
                    bools_end,
                    (rids_start + 1) as nat,
                    rids_end,
                )
            }
            &&& bools[bools_start as int].is_None() ==> {
                &&& rids_match(
                    bools,
                    rids,
                    (bools_start + 1) as nat,
                    bools_end,
                    rids_start,
                    rids_end,
                )
            }
        },
    decreases bools_end - bools_start,
{
    if bools_end == bools_start {
    } else {
        if bools[bools_end - 1].is_Some() {
            rids_match_pop(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                (rids_end - 1) as nat,
            );
        } else {
            rids_match_pop(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end);
        }
    }
}

} // verus!
