#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{
    prelude::*,
    multiset::*,};
use state_machines_macros::tokenized_state_machine;

verus!{

tokenized_state_machine!{
    #[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(T))]
    RwLockSpec<T> {
        fields {
            #[sharding(constant)]
            pub user_inv: Set<T>,

            #[sharding(constant)]
            pub rc_width: int,

            #[sharding(storage_option)]
            pub storage: Option<T>,

            #[sharding(variable)]
            pub exc_locked: bool,

            #[sharding(map)]
            pub ref_counts: Map<int, int>,

            #[sharding(option)]
            pub exc_pending: Option<int>,

            #[sharding(option)]
            pub exc_guard: Option<()>,

            #[sharding(multiset)]
            pub shared_pending: Multiset<int>,

            #[sharding(multiset)]
            pub shared_guard: Multiset<(int, T)>,
        }

        init!{
            initialize(rc_width: int, init_t: T, user_inv: Set<T>,) {
                require(0 < rc_width);
                require(user_inv.contains(init_t));
                init rc_width = rc_width;
                init user_inv = user_inv;
                init storage = Option::Some(init_t);
                init exc_locked = false;
                init ref_counts = Map::new(
                    |i| 0 <= i < rc_width,
                    |i| 0,
                );
                init exc_pending = Option::None;
                init exc_guard = Option::None;
                init shared_pending = Multiset::empty();
                init shared_guard = Multiset::empty();
            }
        }

        transition!{
            exc_start() {
                require(!pre.exc_locked);
                update exc_locked = true;
                add exc_pending += Some(0);
            }
        }

        transition!{
            exc_check_count() {
                remove exc_pending -= Some(let r);
                have ref_counts >= [r => 0];

                add exc_pending += Some(r + 1);
            }
        }

        transition!{
            exc_finish() {
                remove exc_pending -= Some(pre.rc_width);
                add exc_guard += Some(());

                birds_eye let x = pre.storage.get_Some_0();

                withdraw storage -= Some(x);
                assert(pre.user_inv.contains(x));
            }
        }

        transition!{
            exc_release(t: T) {
                require(pre.user_inv.contains(t));
                update exc_locked = false;
                remove exc_guard -= Some(());
                deposit storage += Some(t);
            }
        }

        transition!{
            shared_start(r: int) {
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc + 1];
                add shared_pending += {r};
            }
        }

        transition!{
            shared_abandon(r: int) {
                remove ref_counts -= [r => let rc];
                require(rc > 0);
                add ref_counts += [r => rc - 1];
                remove shared_pending -= {r};
            }
        }

        transition!{
            shared_finish(r: int) {
                require(!pre.exc_locked);
                remove shared_pending -= {r};

                birds_eye let t = pre.storage.get_Some_0();
                add shared_guard += {(r, t)};

                assert(pre.user_inv.contains(t));
            }
        }

        transition!{
            shared_release(val: (int, T)) {
                // require(pre.user_inv.contains(val.1));
                remove shared_guard -= {val};

                let r = val.0;
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc - 1];

                assert(rc > 0) by {
                    assert(0 <= r < pre.rc_width);
                    assert(pre.shared_guard.count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).len() > 0);
                    assert(pre.ref_counts.index(r) > 0);
                };
            }
        }

        property!{
            do_guard(val: (int, T)) {
                have shared_guard >= {val};
                guard storage >= Some(val.1);
            }
        }

        property!{
            rc_not_zero_guard(r: int) {
                have shared_pending >= {r};
                have ref_counts >= [r => let rc];
                assert(rc > 0);
            }
        }


        ///// Invariants and proofs

        #[invariant]
        pub fn sto_user_inv(&self) -> bool {
            self.storage.is_Some() ==>
                self.user_inv.contains(self.storage.get_Some_0())
        }

        #[invariant]
        pub fn ref_counts_domain(&self) -> bool {
            &&& 0 < self.rc_width
            &&& forall |i: int| 0 <= i < self.rc_width <==> self.ref_counts.dom().contains(i)
        }

        #[invariant]
        pub fn exc_inv(&self) -> bool {
            &&& self.exc_locked <==> (self.exc_pending.is_Some() || self.exc_guard.is_Some())
            &&& self.storage.is_Some() <==> self.exc_guard.is_None()
            &&& if let Option::Some(cur_r) = self.exc_pending {
                &&& 0 <= cur_r <= self.rc_width
                &&& self.exc_guard.is_None()
                &&& forall |x| self.shared_guard.count(x) > 0 ==> !(0 <= x.0 < cur_r)
            } else {
                true
            }
        }

        #[invariant]
        pub fn shared_pending_in_range(&self) -> bool {
            forall |r| self.shared_pending.count(r) > 0 ==> (0 <= r < self.rc_width)
        }

        #[invariant]
        pub fn shared_guard_in_range(&self) -> bool {
            forall |x| self.shared_guard.count(x) > 0 ==> (0 <= x.0 < self.rc_width)
        }

        #[invariant]
        pub fn shared_inv_agree(&self) -> bool {
            forall |v| #[trigger] self.shared_guard.count(v) > 0 ==>
                self.storage === Option::Some(v.1)
        }

        pub closed spec fn filter_r(shared_guard: Multiset<(int, T)>, r: int) -> Multiset<(int, T)> {
            shared_guard.filter(|val: (int, T)| val.0 == r)
        }

        #[invariant]
        pub fn shared_counts_agree(&self) -> bool {
            forall |r| 0 <= r < self.rc_width ==>
                #[trigger] self.ref_counts.index(r) ==
                    self.shared_pending.count(r) as int +
                        Self::filter_r(self.shared_guard, r).len() as int
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, rc_width: int, init_t: T,  user_inv: Set<T>) {
            assert forall |r| 0 <= r < post.rc_width implies
                #[trigger] post.ref_counts.index(r) ==
                    post.shared_pending.count(r) as int +
                        Self::filter_r(post.shared_guard, r).len() as int
            by {
                assert(post.ref_counts.index(r) == 0);
                assert(post.shared_pending.count(r) == 0);
                assert(Self::filter_r(post.shared_guard, r) =~= Multiset::empty());
                assert(Self::filter_r(post.shared_guard, r).len() == 0);
            }
            assert(post.shared_counts_agree());
        }

        #[inductive(exc_start)]
        fn exc_start_inductive(pre: Self, post: Self) {

        }

        #[inductive(exc_check_count)]
        fn exc_check_count_inductive(pre: Self, post: Self) {
            let prev_r = pre.exc_pending.get_Some_0();
            assert forall |x| #[trigger] post.shared_guard.count(x) > 0
                && x.0 == prev_r implies false
            by {
                assert(Self::filter_r(post.shared_guard, prev_r).count(x) > 0);
            }
        }

        #[inductive(exc_finish)]
        fn exc_finish_inductive(pre: Self, post: Self) {
        }

        #[inductive(exc_release)]
        fn exc_release_inductive(pre: Self, post: Self, t: T) {

        }

        #[inductive(shared_start)]
        fn shared_start_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_abandon)]
        fn shared_abandon_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_finish)]
        fn shared_finish_inductive(pre: Self, post: Self, r: int) {
            let t = pre.storage.get_Some_0();

            assert forall |r0| 0 <= r0 < post.rc_width implies
                #[trigger] post.ref_counts.index(r0) ==
                    post.shared_pending.count(r0) as int +
                        Self::filter_r(post.shared_guard, r0).len() as int
            by {
                if r == r0 {
                    assert(pre.shared_pending =~= post.shared_pending.add(Multiset::singleton(r)));
                    assert(Self::filter_r(post.shared_guard, r) =~= Self::filter_r(pre.shared_guard, r).add(Multiset::singleton((r, t))));
                    assert(post.ref_counts.index(r0) ==
                        post.shared_pending.count(r0) as int +
                            Self::filter_r(post.shared_guard, r0).len() as int);
                } else {
                    assert(Self::filter_r(post.shared_guard, r0) =~= Self::filter_r(pre.shared_guard, r0));
                    assert(post.ref_counts.index(r0) ==
                        post.shared_pending.count(r0) as int +
                            Self::filter_r(post.shared_guard, r0).len() as int);
                }
            }
        }

        #[inductive(shared_release)]
        fn shared_release_inductive(pre: Self, post: Self, val: (int, T)) {
            let r = val.0;
            assert forall |r0| 0 <= r0 < post.rc_width implies
                #[trigger] post.ref_counts.index(r0) ==
                    post.shared_pending.count(r0) as int +
                        Self::filter_r(post.shared_guard, r0).len() as int
            by {
                if r0 == r {
                    assert(Self::filter_r(pre.shared_guard, r) =~= Self::filter_r(post.shared_guard, r).add(Multiset::singleton(val)));
                } else {
                    assert(Self::filter_r(post.shared_guard, r0) =~= Self::filter_r(pre.shared_guard, r0));
                }
            }
        }
    }
}


} // verus!