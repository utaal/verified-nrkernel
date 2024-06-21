use vstd::prelude::*;

verus!{

pub open spec fn inj_on<A, B>(f: spec_fn(A) -> B, da: Set<A>) -> bool {
    forall|x:A,y:A| da.contains(x) && da.contains(y) && f(x) == f(y) ==> x == y
}

pub proof fn lemma_filter_len_le<A>(f: spec_fn(A) -> bool, da: Set<A>)
    requires da.finite(), // TODO: necessary?
    ensures
        da.filter(f).finite(),
        da.filter(f).len() <= da.len(),
    decreases da.len()
{
    if da.is_empty() {
        assert(da.filter(f) =~= Set::empty());
    } else {
        let x = da.choose();
        lemma_filter_len_le(f, da.remove(x));
        if f(x) {
            assert(da.remove(x).filter(f).insert(x) =~= da.filter(f));
        } else {
            assert(da.remove(x).filter(f) =~= da.filter(f));
        }
    }
}

pub proof fn lemma_map_len_le<A,B>(f: spec_fn(A) -> B, da: Set<A>)
    requires da.finite()
    ensures
        da.map(f).finite(),
        da.map(f).len() <= da.len(),
    decreases da.len()
{
    if da.is_empty() {
        assert(da.map(f) =~= Set::empty());
    } else {
        let x = da.choose();
        lemma_map_len_le(f, da.remove(x));
        assert(da.remove(x).map(f).insert(f(x)) =~= da.map(f));
    }
}

pub proof fn lemma_map_len_eq<A,B>(f: spec_fn(A) -> B, da: Set<A>)
    requires
        da.finite(),
        inj_on(f, da)
    ensures
        da.map(f).finite(),
        da.map(f).len() == da.len(),
    decreases da.len()
{
    if da.is_empty() {
        assert(da.map(f) =~= Set::empty());
    } else {
        let x = da.choose();
        lemma_map_len_eq(f, da.remove(x));
        assert(da.remove(x).map(f).insert(f(x)) =~= da.map(f));
    }
}

/// Creates a finite set of natural numbers in the range [lo, hi).
pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::new(|i: nat| lo <= i && i < hi)
}

/// If a set solely contains numbers in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).finite(),
        set_nat_range(lo, hi).len() == hi - lo,
    decreases hi - lo,
{
    if lo == hi {
        assert(set_nat_range(lo, hi) =~= Set::empty());
    } else {
        lemma_nat_range(lo, sub(hi, 1));
        assert(set_nat_range(lo, sub(hi, 1)).insert(sub(hi, 1)) =~= set_nat_range(lo, hi));
    }
}

//spec fn inj<A, B>(f: spec_fn(A) -> B) -> bool {
//    inj_on(f, univ())
//}
//
//spec fn bij_betw<A, B>(f: spec_fn(A) -> B) -> bool {
//    inj(f) && univ::<A>.map(f) ==
//}

//spec fn univ<A>() -> Set<A> {
//    Set::new(|a:A| true)
//}

}
