#[allow(unused_imports)]
use builtin::*;
use vstd::{ prelude::*, multiset::*};
use state_machines_macros::tokenized_state_machine;


tokenized_state_machine!(RwLockSpec<#[cfg_attr(verus_keep_ghost, verifier::maybe_negative)] T> {
    fields {
        #[sharding(constant)]
        pub user_inv: Set<T>,

        #[sharding(variable)]
        pub flag_exc: bool,

        #[sharding(variable)]
        pub flag_rc: nat,

        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(option)]
        pub pending_writer: Option<()>,

        #[sharding(option)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    init!{
        initialize_full(user_inv: Set<T>, t: T) {
            require(user_inv.contains(t));
            init user_inv = user_inv;
            init flag_exc = false;
            init flag_rc = 0;
            init storage = Option::Some(t);
            init pending_writer = Option::None;
            init writer = Option::None;
            init pending_reader = Multiset::empty();
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_full)]
    fn initialize_full_inductive(post: Self, user_inv: Set<T>, t: T) { }

    /// Increment the 'rc' counter, obtain a pending_reader
    transition!{
        acquire_read_start() {
            update flag_rc = pre.flag_rc + 1;
            add pending_reader += {()};
        }
    }

    /// Exchange the pending_reader for a reader by checking
    /// that the 'exc' bit is 0
    transition!{
        acquire_read_end() {
            require(pre.flag_exc == false);

            remove pending_reader -= {()};

            birds_eye let x: T = pre.storage.get_Some_0();
            add reader += {x};

            assert(pre.user_inv.contains(x));
        }
    }

    /// Decrement the 'rc' counter, abandon the attempt to gain
    /// the 'read' lock.
    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flag_rc >= 1);
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    /// Atomically set 'exc' bit from 'false' to 'true'
    /// Obtain a pending_writer
    transition!{
        acquire_exc_start() {
            require(pre.flag_exc == false);
            update flag_exc = true;
            add pending_writer += Some(());
        }
    }

    /// Finish obtaining the write lock by checking that 'rc' is 0.
    /// Exchange the pending_writer for a writer and withdraw the
    /// stored object.
    transition!{
        acquire_exc_end() {
            require(pre.flag_rc == 0);

            remove pending_writer -= Some(());

            add writer += Some(());

            birds_eye let x = pre.storage.get_Some_0();
            withdraw storage -= Some(x);

            assert(pre.user_inv.contains(x));
        }
    }

    /// Release the write-lock. Update the 'exc' bit back to 'false'.
    /// Return the 'writer' and also deposit an object back into storage.
    transition!{
        release_exc(x: T) {
            require(pre.user_inv.contains(x));
            remove writer -= Some(());

            update flag_exc = false;

            deposit storage += Some(x);
        }
    }

    /// Check that the 'reader' is actually a guard for the given object.
    property!{
        read_guard(x: T) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    property!{
        read_match(x: T, y: T) {
            have reader >= {x};
            have reader >= {y};
            assert(equal(x, y));
        }
    }

    /// Release the reader-lock. Decrement 'rc' and return the 'reader' object.
    #[transition]
    transition!{
        release_shared(x: T) {
            remove reader -= {x};

            assert(pre.flag_rc >= 1) by {
                //assert(pre.reader.count(x) >= 1);
                assert(equal(pre.storage, Option::Some(x)));
                //assert(equal(x, pre.storage.get_Some_0()));
            };
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flag_exc { 1 } else { 0 as int }) ==
            (if self.pending_writer.is_Some() { 1 } else { 0 as int }) as int
            + (if self.writer.is_Some() { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flag_rc == self.pending_reader.count(())
            + self.reader.count(self.storage.get_Some_0())
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: T| #[trigger] self.reader.count(t) > 0 ==> equal(self.storage, Option::Some(t))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        self.writer.is_Some() ==> self.storage.is_None()
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        self.storage.is_None() ==> self.writer.is_Some()
    }

    #[invariant]
    pub fn sto_user_inv(&self) -> bool {
        self.storage.is_Some() ==>
            self.user_inv.contains(self.storage.get_Some_0())
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: T) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self, x: T) {
        assert(equal(pre.storage, Option::Some(x)));
    }
});
