
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::seq::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::set::Set;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::map::Map;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::arbitrary;

verus!{

pub open spec fn seq_unique<A>(seq: Seq<A>) -> bool
    // where A: PartialEq + Structural
{
    forall(|i:int, j:int| (0 <= i < seq.len() && 0 <=j < seq.len() && i != j)
            ==> seq.index(i as int) !== seq.index(j as int))
}

/// whether two sequences are disjoint, i.e., they don't have common elements
pub open spec fn seq_disjoint<A>(s: Seq<A>, t: Seq<A>) -> bool
{
   forall(|i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j))
}


pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set(seq.drop_last()).insert(seq.last())
    }
}


pub proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures seq_to_set(seq).finite()
    decreases seq.len()
{
    if seq.len() > 0 {
        let sub_set = seq_to_set(seq.drop_last());
        assert(sub_set.finite()) by {
            seq_to_set_is_finite(seq.drop_last());
        }
        assert(seq_to_set(seq) == sub_set.insert(seq.last()));
    }
}

pub proof fn seq_to_set_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) ==> seq_to_set(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        let elm = seq.last();
        let sub_req = seq.drop_last();
        let sub_set = seq_to_set(sub_req);
        assert(forall |a| #[trigger] sub_req.contains(a) ==> seq_to_set(sub_req).contains(a)) by {
            seq_to_set_contains(sub_req);
        }

        assert(seq.ext_equal(sub_req.push(elm)));

        assert forall |a| #[trigger] sub_req.push(elm).contains(a) implies seq_to_set(seq).contains(a) by {
            if sub_req.contains(a) {
                assert(seq_to_set(seq).contains(a));
            }
            if a == elm {
                assert(seq_to_set(seq).contains(elm));
            }
        }
    }
}


pub open spec fn map_contains_value<K, V>(map: Map<K, V>, val: V) -> bool
    // where K: PartialEq + Structural
{
    exists|i: K| #[trigger] map.dom().contains(i) && map.index(i) == val
}


pub closed spec fn get_new_nat(s: Set<nat>, t: Set<nat>) -> nat {
    arbitrary() // TODO
}

pub open spec fn range(low: nat, mid: nat, high:nat) -> bool {
    low <= mid && mid < high
}

pub open spec fn rangeincl(low: nat, mid: nat, high:nat) -> bool {
    low <= mid && mid <= high
}


pub proof fn get_new_nat_not_in(s: Set<nat>,t: Set<nat>,) {
    requires([
        s.finite(),
        t.finite(),
    ]);

    ensures([
        !s.contains(get_new_nat(s, t)),
        !t.contains(get_new_nat(s, t)),
    ]);

    assume(false); // TODO
}


#[verifier(nonlinear)]
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires 0 <= i < len, len > 0
    ensures  (i % len) == i

{
}






// pub proof fn mod_range_not_same1(i: int, j: int)
//     requires
//       16 > 0,
//       i < j < i + 16
//     ensures
//       i % 16 != j % 16
// {
// }

// #[verifier(nonlinear)]
// pub proof fn mod_range_not_same(i: int, j: int, N: int)
//     requires
//       N > 0,
//       i < j < i + N
//     ensures
//       i % N != j % N
// {
//     let ki = i / N;
//     let kj = j / N;

//     assert(ki * N <= i < (ki + 1) * N);
//     assert(kj * N <= j < (kj + 1) * N);

//     // assert(i % N == i - ki * N);
//     // assert(j % N == j - kj * N);

//     // assert(i - ki * N != j - kj * N);
//     assert(false);
// }

}
