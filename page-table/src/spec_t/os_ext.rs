use vstd::prelude::*;
use crate::spec_t::mmu::defs::{ Core, MemRegion };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ overlap, aligned };


verus! {

// This is the extra/external part of the OS. It specifies the kernel lock, (de-)allocation, and
// shootdown coordination

pub enum Lbl {
    Tau,
    AcquireLock { core: Core },
    ReleaseLock { core: Core },
    InitShootdown { core: Core, vaddr: nat },
    AckShootdown { core: Core },
    Allocate { core: Core, res: MemRegion },
    Deallocate { core: Core, reg: MemRegion },
}

pub struct State {
    pub lock: Option<Core>,
    pub shootdown_vec: ShootdownVector,
    pub allocated: Set<MemRegion>,
}

pub struct ShootdownVector {
    pub vaddr: nat,
    pub open_requests: Set<Core>,
}

pub struct Constants {
    pub node_count: nat,
    pub core_count: nat,
}

impl Constants {
    // FIXME: This is duplicated in mmu constants. Can we somehow get rid of one of these?
    #[verifier(opaque)]
    pub open spec fn valid_core(self, core: Core) -> bool {
        &&& core.node_id < self.node_count
        &&& core.core_id < self.core_count
    }
}

impl State {
    pub open spec fn disjoint_from_allocations(self, reg: MemRegion) -> bool {
        forall|reg2| #[trigger] self.allocated.contains(reg2) ==> !overlap(reg, reg2)
    }
}

pub enum Step {
    AcquireLock,
    ReleaseLock,
    InitShootdown,
    AckShootdown,
    Allocate,
    Deallocate
}

// State machine transitions

pub open spec fn step_AcquireLock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::AcquireLock { core }

    &&& c.valid_core(core)
    &&& pre.lock is None

    &&& post == State {
        lock: Some(core),
        ..pre
    }
}

pub open spec fn step_ReleaseLock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::ReleaseLock { core }

    &&& c.valid_core(core)
    &&& pre.lock == Some(core)

    &&& post == State {
        lock: None,
        ..pre
    }
}

// This initiates a shootdown for all other cores in the system, so we don't take the cores as an
// argument.
pub open spec fn step_InitShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::InitShootdown { core, vaddr }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests === set![]

    &&& post == State {
        shootdown_vec: ShootdownVector {
            vaddr,
            open_requests: Set::new(|core| c.valid_core(core))
        },
        ..pre
    }
}

pub open spec fn step_AckShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::AckShootdown { core }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests.contains(core)

    &&& post == State {
        shootdown_vec: ShootdownVector {
            open_requests: pre.shootdown_vec.open_requests.remove(core),
            ..pre.shootdown_vec
        },
        ..pre
    }
}

// TODO: Hardcoding 4k allocations for now. Should fix that to support large mappings.
pub open spec fn step_Allocate(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Allocate { core, res }

    &&& c.valid_core(core)
    &&& pre.disjoint_from_allocations(res)
    &&& aligned(res.base, 4096)
    &&& res.size == 4096

    &&& post == State {
        allocated: pre.allocated.insert(res),
        ..pre
    }
}

pub open spec fn step_Deallocate(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Deallocate { core, reg }

    &&& c.valid_core(core)
    &&& pre.allocated.contains(reg)

    &&& post == State {
        allocated: pre.allocated.remove(reg),
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::AcquireLock   => step_AcquireLock(pre, post, c, lbl),
        Step::ReleaseLock   => step_ReleaseLock(pre, post, c, lbl),
        Step::InitShootdown => step_InitShootdown(pre, post, c, lbl),
        Step::AckShootdown  => step_AckShootdown(pre, post, c, lbl),
        Step::Allocate      => step_Allocate(pre, post, c, lbl),
        Step::Deallocate    => step_Deallocate(pre, post, c, lbl),
    }
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.lock === None
    &&& pre.shootdown_vec.open_requests === set![]
    &&& pre.allocated === set![]
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}





//// Invariants for this state machine
//
//impl State {
//    pub open spec fn wf(self, c: Constants) -> bool {
//        &&& forall|core| self.shootdown_vec.open_requests.contains(core) ==> #[trigger] c.valid_core(core)
//    }
//
//    pub open spec fn inv(self, c: Constants) -> bool {
//        &&& self.wf(c)
//    }
//} // impl State
//
//
//pub proof fn init_implies_inv(pre: State, c: Constants)
//    requires init(pre, c)
//    ensures pre.inv(c)
//{}
//
//pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
//    requires
//        pre.inv(c),
//        next(pre, post, c, lbl),
//    ensures post.inv(c)
//{}



/// The axiomatized interface to execute the actions specified in this state machine.
pub mod code {
    use vstd::prelude::*;
    use crate::spec_t::os_ext;
    use crate::spec_t::mmu::defs::{ Core, MemRegionExec, PAGE_SIZE };
    use crate::theorem::TokState;

    #[verifier(external_body)]
    pub tracked struct Token {}

    impl Token {
        pub spec fn consts(self) -> os_ext::Constants;
        pub spec fn core(self) -> Core;
        pub spec fn pre(self) -> os_ext::State;
        pub spec fn post(self) -> os_ext::State;
        pub spec fn lbl(self) -> os_ext::Lbl;
        pub spec fn tstate(self) -> TokState;

        pub open spec fn set_valid(self, new: Token) -> bool {
            &&& new.consts() == self.consts()
            &&& new.core() == self.core()
            &&& new.pre() == self.pre()
            &&& new.post() == self.post()
            &&& new.lbl() == self.lbl()
            &&& new.tstate() is Validated
        }

        pub open spec fn prophesied_step(self, new: Token) -> bool {
            &&& new.consts() == self.consts()
            &&& new.core() == self.core()
            &&& new.pre() == self.pre()
            &&& new.tstate() is ProphecyMade
            &&& os_ext::next(new.pre(), new.post(), new.consts(), new.lbl())
        }

        // FIXME: Allowing multiple calls to prophesy functions is unsound because they can give
        // potentially conflicting information about the pre state, which remains unchanged on each call.
        pub proof fn prophesy_acquire_lock(tracked &mut self)
            requires
                //old(self).consts().valid_core(old(self).core()), TODO: ??
                old(self).tstate() is Init,
            ensures
                self.lbl() == (os_ext::Lbl::AcquireLock { core: self.core() }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        // TODO: Requiring that we hold the lock here is a bit weird because in the
        // transitions we don't really distinguish which preconditions are ones that the
        // user has to satisfy and which ones are consequences of executing the function.
        // But it's probably fine? The function just has to be specified in a way that
        // makes sense.
        //
        // We have enabling conditions that need to be ensured by the caller and "technical"
        // enabling conditions, which are guaranteed by executing the function. In the first case,
        // the user must show that after an arbitrary sequence of concurrent transitions the
        // condition holds. In the second case, this is a guarantee obtained from the function that
        // must not conflict with what we can derive ourselves from the concurrent transitions.
        //
        // TODO: is it still fine if it's on the prophesy call?
        pub proof fn prophesy_release_lock(tracked &mut self)
            requires
                old(self).tstate() is Init,
                old(self).pre().lock == Some(old(self).core())
            ensures
                self.lbl() == (os_ext::Lbl::ReleaseLock { core: self.core() }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_init_shootdown(tracked &mut self, vaddr: usize)
            requires
                old(self).tstate() is Init,
            ensures
                self.lbl() == (os_ext::Lbl::InitShootdown { core: self.core(), vaddr: vaddr as nat }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_ack_shootdown(tracked &mut self)
            requires
                old(self).tstate() is Init,
            ensures
                self.lbl() == (os_ext::Lbl::AckShootdown { core: self.core() }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_allocate(tracked &mut self)
            requires
                old(self).tstate() is Init,
            ensures
                self.lbl() is Allocate,
                self.lbl()->Allocate_core == self.core(),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_deallocate(tracked &mut self, reg: MemRegionExec)
            requires
                old(self).tstate() is Init,
                old(self).pre().allocated.contains(reg@),
            ensures
                self.lbl() == (os_ext::Lbl::Deallocate { core: self.core(), reg: reg@ }),
                old(self).prophesied_step(*self),
        {
            admit();
        }
    }

    // External interface to the  memory allocation of the linux module
    #[cfg(feature="linuxmodule")]
    extern "C" {
        fn mmap_pgtable_lock();
        fn mmap_mm_pgtable_lock(mm: u64);
        fn mmap_pgtable_unlock();
        fn mmap_mm_pgtable_unlock(mm: u64);
    }

    #[cfg(not(feature="linuxmodule"))]
    use std::sync::atomic::{AtomicBool, Ordering::{Acquire, Release}};

    /// global variable representing the page table lock
    #[cfg(not(feature="linuxmodule"))]
    exec static PGTABLE_LOCK: AtomicBool = AtomicBool::new(false);

    /// acquires the page table spinlock
    #[cfg(not(feature="linuxmodule"))]
    #[verifier(external_body)]
    unsafe fn mmap_pgtable_lock() {
        while PGTABLE_LOCK.swap(true, Acquire) {
            std::hint::spin_loop();
        }
    }

    /// releases the page table spinlock
    #[cfg(not(feature="linuxmodule"))]
    #[verifier(external_body)]
    unsafe fn mmap_pgtable_unlock() {
        PGTABLE_LOCK.store(false, Release);
    }


    /// acquires the page table lock
    /// 
    /// TODO: ideally this takes the lock pointer
    #[verifier(external_body)]
    pub exec fn acquire_lock(Tracked(tok): Tracked<&mut Token>)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::AcquireLock { core: old(tok).core() }),
        ensures
            tok.tstate() is Spent,
    {
        unsafe { mmap_pgtable_lock(); }
    }

    /// releases the page table lock
    /// 
    /// TODO: ideally this takes the lock pointer
    #[verifier(external_body)]
    pub exec fn release_lock(Tracked(tok): Tracked<&mut Token>)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::ReleaseLock { core: old(tok).core() }),
        ensures
            tok.tstate() is Spent,
    {
        unsafe { mmap_pgtable_unlock(); }
    }

    // External interface to the TLB maintenance operations of the current OS
    #[cfg(feature="linuxmodule")]
    extern "C" {
        /// invalidates a range of tlb pages for the current mm
        fn flush_tlb_mm_range(mm: u64, start: u64, end: u64, stride: u64, freed_tables: bool);

        /// invalidates a tlb page for the given start address and the current mm
        fn flush_tlb_page(start: u64, page_size: u64);
    }

    /// initiates a shootdown for a given virtual page of a given size
    /// 
    /// this only covers tlb invalidations of a single page at `vaddr` with a page size of `size`
    #[verifier(external_body)]
    pub exec fn init_shootdown(Tracked(tok): Tracked<&mut Token>, vaddr: usize, size: usize)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::InitShootdown { core: old(tok).core(), vaddr: vaddr as nat }),
        ensures
            tok.tstate() is Spent,
    {
        // on linux this is a blocking call to flush the TLB for the given page. 
        #[cfg(feature="linuxmodule")]
        unsafe { flush_tlb_page(vaddr as u64, size as u64); }

        // #[cfg(not(feature="linuxmodule"))]
        // implementation of the shootdown is not necessary if we run this as an standalone module
    }

    /// handles processing of the TLB shootdown on a core, acknowledging that the local invalidation has been completed
    #[verifier(external_body)]
    pub exec fn ack_shootdown(Tracked(tok): Tracked<&mut Token>)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::AckShootdown { core: old(tok).core() }),
        ensures
            tok.tstate() is Spent,
    {
        // #[cfg(feature="linuxmodule")]
        // implementation of the shootdown acknowledgement in Linux is not necessary, as `flush_tlb_page` is blocking. 
        
        // #[cfg(not(feature="linuxmodule"))]
        // implementation for the standalone module is not neccessary as this runs in user space.
    }


    // External interface to the  memory allocation of the linux module
    #[cfg(feature="linuxmodule")]
    extern "C" {
        /// Allocates memory for a page table node when compiling for use in the Linux Kernel Module
        fn pt_memory_alloc(sz: usize, align: u64, level: u8) -> u64;
        /// Frees memory of a page table node when compiling for use in the Linux Kernel Module
        fn pt_memory_free(pa: u64, sz: usize, level: u8);
    }

    /// Allocates memory for a page table node in the standalone case
    #[cfg(not(feature="linuxmodule"))]
    #[verifier(external_body)]
    unsafe fn pt_memory_alloc(sz: usize, align: u64, level: u8) -> u64 {
        let layout = std::alloc::Layout::from_size_align_unchecked(sz, PAGE_SIZE);
        let ptr = std::alloc::alloc_zeroed(layout);
        if ptr.is_null() {
            panic!("Failed to allocate memory");
        }
        ptr as u64
    }

    /// Frees memory for a page table node in the standalone case
    #[cfg(not(feature="linuxmodule"))]
    #[verifier(external_body)]
    unsafe fn pt_memory_free(pa: u64, sz: usize, level: u8) {
        let layout = std::alloc::Layout::from_size_align_unchecked(sz, PAGE_SIZE);
        std::alloc::dealloc(std::mem::transmute(pa), layout);
    }

    /// Allocates memory for a page table node
    /// 
    /// the `layer` is used here to give a *hint* to the allocator which level of the page table we're allocating for. 
    /// (Note: this is mainly here due to the way Linux allocates memory for page tables)
    #[verifier(external_body)]
    pub exec fn allocate(Tracked(tok): Tracked<&mut Token>, layer: usize) -> (res: MemRegionExec)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() matches os_ext::Lbl::Allocate { core: lbl_core, .. } && lbl_core == old(tok).core(),
        ensures
            tok.tstate() is Spent,
            res@ == old(tok).lbl()->Allocate_res,
    {
        let addr = unsafe { pt_memory_alloc(PAGE_SIZE, PAGE_SIZE as u64, layer.try_into().unwrap()) };
        MemRegionExec { base: addr.try_into().unwrap(), size: PAGE_SIZE }
    }

    /// Frees memory of a page table node at a given layer.
    /// 
    /// the `layer` is used here as a *hint* to the allocator which level of the page table this memory was used for. 
    /// (Note: this is mainly here due to the way Linux allocates memory for page tables)
    #[verifier(external_body)]
    pub exec fn deallocate(Tracked(tok): Tracked<&mut Token>, reg: MemRegionExec, layer: usize)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::Deallocate { core: old(tok).core(), reg: reg@ }),
        ensures
            tok.tstate() is Spent,
    {
        unsafe { pt_memory_free(reg.base.try_into().unwrap(), reg.size, layer.try_into().unwrap()) };
    }
}

} // verus!
