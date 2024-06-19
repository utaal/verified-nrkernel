// Verified Node Replication Library
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::set::Set;

verus! {

pub open spec fn seq_unique<A>(
    seq: Seq<A>,
) -> bool
// where A: PartialEq + Structural
 {
    forall|i: int, j: int|
        (0 <= i < seq.len() && 0 <= j < seq.len() && i != j) ==> seq.index(i as int) !== seq.index(
            j as int,
        )
}

/// whether two sequences are disjoint, i.e., they don't have common elements
pub open spec fn seq_disjoint<A>(s: Seq<A>, t: Seq<A>) -> bool {
    forall|i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j)
}

/// recursive definition of seq to set conversion
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
    when seq.len() >= 0
    via seq_to_set_rec_decreases::<A>
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

#[via_fn]
proof fn seq_to_set_rec_decreases<A>(seq: Seq<A>) {
    if seq.len() == 0 {
    } else {
        assert(seq.drop_last().len() < seq.len());  // INCOMPLETENESS weird incompleteness again
    }
}

/// shows that the recursive definition of set_to_seq produces a finite set
proof fn seq_to_set_rec_is_finite<A>(seq: Seq<A>)
    ensures
        seq_to_set_rec(seq).finite(),
    decreases seq.len(),
{
    if seq.len() > 0 {
        let sub_seq = seq.drop_last();
        assert(seq_to_set_rec(sub_seq).finite()) by {
            seq_to_set_rec_is_finite(sub_seq);
        }
    }
}

/// shows that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures
        forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a),
    decreases seq.len(),
{
    if seq.len() > 0 {
        assert(forall|a| #[trigger]
            seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }
        assert(seq =~= seq.drop_last().push(seq.last()));
        assert forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures
        seq_to_set(seq) == seq_to_set_rec(seq),
{
    assert(forall|n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall|n| #[trigger] seq.contains(n) <==> seq_to_set(seq).contains(n));
    assert(seq_to_set(seq) =~= seq_to_set_rec(seq));
}

pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A> {
    Set::new(|a: A| seq.contains(a))
}

pub proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures
        seq_to_set(seq).finite(),
{
    assert(seq_to_set(seq).finite()) by {
        seq_to_set_equal_rec(seq);
        seq_to_set_rec_is_finite(seq);
    }
}

pub open spec fn map_new_rec<V>(dom: nat, val: V) -> Map<nat, V>
    decreases dom,
    when dom >= 0
{
    if dom == 0 {
        map![ dom => val]
    } else {
        map_new_rec((dom - 1) as nat, val).insert(dom, val)
    }
}

pub proof fn map_new_rec_dom_finite<V>(dom: nat, val: V)
    ensures
        map_new_rec(dom, val).dom().finite(),
        forall|n: nat| 0 <= n <= dom <==> map_new_rec(dom, val).contains_key(n),
        forall|n|
            (#[trigger] map_new_rec(dom, val).contains_key(n)) ==> map_new_rec(dom, val)[n] == val,
    decreases dom,
{
    if dom == 0 {
    } else {
        let sub_dom = (dom - 1) as nat;
        let sub_map = map_new_rec(sub_dom as nat, val);
        assert(sub_map.dom().finite()) by {
            map_new_rec_dom_finite(sub_dom, val);
        }
        assert(forall|n: nat| (#[trigger] sub_map.contains_key(n)) <==> 0 <= n <= sub_dom) by {
            map_new_rec_dom_finite(sub_dom, val);
        }
        assert(forall|n: nat| (#[trigger] sub_map.contains_key(n)) ==> sub_map[n] == val) by {
            map_new_rec_dom_finite(sub_dom, val);
        }
    }
}

pub open spec fn map_contains_value<K, V>(
    map: Map<K, V>,
    val: V,
) -> bool
// where K: PartialEq + Structural
 {
    exists|i: K| #[trigger] map.contains_key(i) && map.index(i) == val
}

pub open spec fn range(low: nat, mid: nat, high: nat) -> bool {
    low <= mid && mid < high
}

pub open spec fn rangeincl(low: nat, mid: nat, high: nat) -> bool {
    low <= mid && mid <= high
}

#[verifier(nonlinear)]
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires
        0 <= i < len,
        len > 0,
    ensures
        (i % len) == i,
{
}

} // verus!
