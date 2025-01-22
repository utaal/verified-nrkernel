#![verus::trusted]
// trusted:
// this defines the page table structure as interpreted by the hardware
// and the hardware state machine

use vstd::prelude::*;
use crate::definitions_t::{
    aligned, axiom_max_phyaddr_width_facts, between, bit, bitmask_inc, Flags, HWRWOp, MemRegion,
    PTE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_PHYADDR_WIDTH,
    PAGE_SIZE, Core,
};
use crate::spec_t::mem::{self, word_index_spec};
use crate::spec_t::mmu::{self, pt_mem, WalkResult};

verus! {

pub struct Constants {
    pub node_count: nat,
    pub core_count: nat,
    pub phys_mem_size: nat,
}

pub struct State<M: mmu::MMU> {
    /// Word-indexed physical memory
    pub mem: Seq<nat>,
    pub nodes: Map<nat, PerNodeState>,
    pub mmu: M,
}

// State for each NUMA node
pub struct PerNodeState {
    pub cores: Map<nat, PerCoreState>,
}

// State for each core
pub struct PerCoreState {
    pub tlb: Map<nat, PTE>,
}

#[allow(inconsistent_fields)]
pub enum Step {
    Invlpg { core: Core, vaddr: usize },
    MMUStep { lbl: mmu::Lbl },
    ReadWrite {
        vaddr: nat,
        paddr: nat,
        op: HWRWOp,
        walk_result: WalkResult,
        core: Core,
    },
    TLBFill { vaddr: usize, pte: PTE, core: Core },
    TLBEvict { vaddr: nat, core: Core },
    Stutter,
}

// FIXME: Including is_variant conditionally to avoid the warning when not building impl. But this
// should disappear completely when I find the time to migrate to the new syntax.
#[cfg_attr(feature = "impl", is_variant)]
pub ghost enum GPDE {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        ///// Accessed; indicates whether software has accessed the page referenced by this entry
        //A: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        ///// Accessed; indicates whether software has accessed the page referenced by this entry
        //A: bool,
        ///// Dirty; indicates whether software has written to the page referenced by this entry
        //D: bool,
        // /// Page size; must be 1 (otherwise, this entry references a directory)
        // PS: Option<bool>,
        // PS is entirely determined by the Page variant and the layer
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    /// An `Empty` entry is an entry that does not contain a valid mapping. I.e. the entry is
    /// either empty or has a bit set that the intel manual designates as must-be-zero. Both empty
    /// and invalid entries cause a page fault if used during translation.
    Empty,
}

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table
// MASK_FLAG_* are flags valid for entries at all levels.
pub const MASK_FLAG_P: usize = bit!(0usize);

pub const MASK_FLAG_RW: usize = bit!(1usize);

pub const MASK_FLAG_US: usize = bit!(2usize);

pub const MASK_FLAG_PWT: usize = bit!(3usize);

pub const MASK_FLAG_PCD: usize = bit!(4usize);

//pub const MASK_FLAG_A: usize = bit!(5usize);

pub const MASK_FLAG_XD: usize = bit!(63usize);

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
//pub const MASK_PG_FLAG_D: usize = bit!(6usize);

pub const MASK_PG_FLAG_G: usize = bit!(8usize);

pub const MASK_PG_FLAG_PAT: usize = bit!(12usize);

pub const MASK_L1_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L2_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L3_PG_FLAG_PAT: usize = bit!(7usize);

pub const MASK_DIRTY_ACCESS: usize = bit!(5) | bit!(6);
pub const MASK_NEG_DIRTY_ACCESS: usize = !MASK_DIRTY_ACCESS;

// In the implementation we can always use the 12:52 mask as the invariant guarantees that in the
// other cases, the lower bits are already zero anyway.
// We cannot use dual exec/spec constants here because for those Verus currently doesn't support
// manually guiding the no-overflow proofs.
pub spec const MASK_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_ADDR_SPEC)]
pub exec const MASK_ADDR: usize ensures MASK_ADDR == MASK_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L1_PG_ADDR_SPEC: usize = bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L1_PG_ADDR_SPEC)]
pub exec const MASK_L1_PG_ADDR: usize ensures MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L2_PG_ADDR_SPEC: usize = bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L2_PG_ADDR_SPEC)]
pub exec const MASK_L2_PG_ADDR: usize ensures MASK_L2_PG_ADDR == MASK_L2_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L3_PG_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L3_PG_ADDR_SPEC)]
pub exec const MASK_L3_PG_ADDR: usize ensures MASK_L3_PG_ADDR == MASK_L3_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_DIR_ADDR_SPEC: usize = MASK_ADDR;

#[verifier::when_used_as_spec(MASK_DIR_ADDR_SPEC)]
pub exec const MASK_DIR_ADDR: usize ensures MASK_DIR_ADDR == MASK_DIR_ADDR_SPEC {
    MASK_ADDR
}

#[allow(repr_transparent_external_private_fields)]
// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PDE {
    pub entry: usize,
    pub layer: Ghost<nat>,
}

// Don't broadcast this. It refuses to trigger for some reason.
pub proof fn lemma_bit_indices_less_512(va: usize)
    ensures
        l0_bits!(va) < 512,
        l1_bits!(va) < 512,
        l2_bits!(va) < 512,
        l3_bits!(va) < 512,
{
    assert(l0_bits!(va) < 512) by (bit_vector);
    assert(l1_bits!(va) < 512) by (bit_vector);
    assert(l2_bits!(va) < 512) by (bit_vector);
    assert(l3_bits!(va) < 512) by (bit_vector);
}

// This impl defines everything necessary for the page table walk semantics.
// PDE is reused in the implementation, which has an additional impl block for it in
// `impl_u::l2_impl`.
impl PDE {
    // Could prove that the address is smaller than MAX_PHYADDR but this bound is sufficient sof ar
    pub broadcast proof fn lemma_view_addr_aligned(self)
        requires self.layer@ < 4
        ensures #![trigger self.view()]
            self@ is Directory ==> {
                &&& aligned(self@->Directory_addr as nat, 4096)
                &&& aligned(self@->Directory_addr as nat, 8)
                &&& self@->Directory_addr < usize::MAX - 4096
            },
            self@ is Page ==> {
                &&& aligned(self@->Page_addr as nat, 4096)
                &&& aligned(self@->Page_addr as nat, 8)
                &&& self@->Page_addr < usize::MAX - 4096
            },
    {
        axiom_max_phyaddr_width_facts();
        let mw = MAX_PHYADDR_WIDTH;
        let e = self.entry;
        assert((e & bitmask_inc!(12usize, mw - 1)) % 4096 == 0) by (bit_vector);
        assert((e & bitmask_inc!(21usize, mw - 1)) % 4096 == 0) by (bit_vector);
        assert((e & bitmask_inc!(30usize, mw - 1)) % 4096 == 0) by (bit_vector);
        assert((e & bitmask_inc!(12usize, mw - 1)) < u64::MAX - 4096) by (bit_vector)
            requires 32 <= mw <= 52;
        assert((e & bitmask_inc!(21usize, mw - 1)) < u64::MAX - 4096) by (bit_vector)
            requires 32 <= mw <= 52;
        assert((e & bitmask_inc!(30usize, mw - 1)) < u64::MAX - 4096) by (bit_vector)
            requires 32 <= mw <= 52;
    }

    pub broadcast proof fn lemma_view_unchanged_dirty_access(self, other: PDE)
        requires
            self.layer@ < 4,
            #[trigger] (self.entry & MASK_NEG_DIRTY_ACCESS)
                == #[trigger] (other.entry & MASK_NEG_DIRTY_ACCESS),
            self.layer == other.layer,
        ensures other@ == self@
    {
        reveal(PDE::all_mb0_bits_are_zero);
        let v1 = self.entry;
        let v2 = other.entry;
        assert(forall|b: usize| 0 <= b < 5 ==> #[trigger] (v1 & bit!(b)) == v2 & bit!(b)) by (bit_vector)
            requires v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6));
        assert(forall|b: usize| 6 < b < 64 ==> #[trigger] (v1 & bit!(b)) == v2 & bit!(b)) by (bit_vector)
            requires v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6));
        axiom_max_phyaddr_width_facts();
        let mw = MAX_PHYADDR_WIDTH;

        assert(v1 & bitmask_inc!(12usize, mw - 1)
            == v2 & bitmask_inc!(12usize, mw - 1)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52;
        assert(v1 & bitmask_inc!(21usize, mw - 1)
            == v2 & bitmask_inc!(21usize, mw - 1)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52;
        assert(v1 & bitmask_inc!(30usize, mw - 1)
            == v2 & bitmask_inc!(30usize, mw - 1)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52;
        assert(v1 & bitmask_inc!(mw, 51) == v2 & bitmask_inc!(mw, 51)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52;
        assert(v1 & bitmask_inc!(mw, 62) == v2 & bitmask_inc!(mw, 62)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52;
        assert(v1 & bitmask_inc!(13, 29) == v2 & bitmask_inc!(13, 29)) by (bit_vector)
            requires v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6));
        assert(v1 & bitmask_inc!(13, 20) == v2 & bitmask_inc!(13, 20)) by (bit_vector)
            requires v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6));
    }

    pub open spec fn view(self) -> GPDE {
        let v = self.entry;
        let P   = v & MASK_FLAG_P    == MASK_FLAG_P;
        let RW  = v & MASK_FLAG_RW   == MASK_FLAG_RW;
        let US  = v & MASK_FLAG_US   == MASK_FLAG_US;
        let PWT = v & MASK_FLAG_PWT  == MASK_FLAG_PWT;
        let PCD = v & MASK_FLAG_PCD  == MASK_FLAG_PCD;
        let XD  = v & MASK_FLAG_XD   == MASK_FLAG_XD;
        let G   = v & MASK_PG_FLAG_G == MASK_PG_FLAG_G;
        if v & MASK_FLAG_P == MASK_FLAG_P && self.all_mb0_bits_are_zero() {
            if self.layer == 0 {
                let addr = v & MASK_ADDR;
                GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
            } else if self.layer == 1 {
                if v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // super page mapping
                    let addr = v & MASK_L1_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 2 {
                if v & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // huge page mapping
                    let addr = v & MASK_L2_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 3 {
                let addr = v & MASK_L3_PG_ADDR;
                let PAT = v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT;
                GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
            } else {
                arbitrary()
            }
        } else {
            GPDE::Empty
        }
    }

    /// Returns `true` iff all must-be-zero bits for a given entry are zero.
    #[verifier::opaque]
    pub open spec fn all_mb0_bits_are_zero(self) -> bool {
        if self.entry & MASK_FLAG_P == MASK_FLAG_P {
            if self.layer == 0 {  // PML4, always directory
                // 51:M, 7
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                &&& self.entry & bit!(7usize) == 0
            } else if self.layer == 1 {  // PDPT
                if self.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // 51:M, 29:13
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                    &&& self.entry & bitmask_inc!(13usize,29usize) == 0
                } else {
                    // 51:M, 7
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                    &&& self.entry & bit!(7usize) == 0
                }
            } else if self.layer == 2 {  // PD
                if self.entry & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // 62:M, 20:13
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                    &&& self.entry & bitmask_inc!(13usize,20usize) == 0
                } else {
                    // 62:M, 7
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                    &&& self.entry & bit!(7usize) == 0
                }
            } else if self.layer == 3 {  // PT, always frame
                // 62:M
                self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
            } else {
                arbitrary()
            }
        } else {
            // No bits are reserved for unused entries
            true
        }
    }

    pub open spec fn layer(self) -> nat {
        self.layer@
    }
}

impl Flags {
    pub open spec fn from_GPDEs(pdes: Seq<GPDE>) -> Flags
        recommends
            pdes.len() > 0,
            forall|i| 0 <= i < pdes.len() ==> !(pdes[i] is Empty)
        decreases pdes.len()
    {
        if pdes.len() <= 1 {
            Flags::from_GPDE(pdes[0])
        } else {
            Flags::from_GPDEs(pdes.drop_first()).combine(Flags::from_GPDE(pdes[0]))
        }
    }

    pub open spec fn from_GPDE(pde: GPDE) -> Flags
        recommends !(pde is Empty)
    {
        match pde {
            GPDE::Directory { RW, US, XD, .. } =>
                Flags::from_bits(RW, US, XD),
            GPDE::Page { RW, US, XD, .. } =>
                Flags::from_bits(RW, US, XD),
            _ => arbitrary(),
        }
    }
}


#[allow(unused_macros)]
macro_rules! l0_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(39usize,47usize)) >> 39usize }
}

pub(crate) use l0_bits;

#[allow(unused_macros)]
macro_rules! l1_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(30usize,38usize)) >> 30usize }
}

pub(crate) use l1_bits;

#[allow(unused_macros)]
macro_rules! l2_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(21usize,29usize)) >> 21usize }
}

pub(crate) use l2_bits;

#[allow(unused_macros)]
macro_rules! l3_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(12usize,20usize)) >> 12usize }
}

pub(crate) use l3_bits;

pub open spec fn read_entry(
    pt_mem: mem::PageTableMemory,
    dir_addr: nat,
    layer: nat,
    idx: nat,
) -> GPDE {
    let region = MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat };
    PDE { entry: pt_mem.spec_read(idx, region), layer: Ghost(layer) }@
}

/// TODO: list 4-level paging no HLAT etc. as assumptions (+ the register to enable XD semantics,
/// it's must-be-zero otherwise)
///
/// The intended semantics for valid_pt_walk is this:
/// Given a `PageTableMemory` `pt_mem`, the predicate is true for those `addr` and `pte` where the
/// MMU's page table walk arrives at an entry mapping the frame `pte.frame`. The properties in
/// `pte.flags` reflect the properties along the translation path. I.e. `pte.flags.is_writable` is
/// true iff the RW flag is set in all directories along the translation path and in the frame
/// mapping. Similarly, `pte.flags.is_supervisor` is true iff the US flag is unset in all those
/// structures and `pte.flags.disable_execute` is true iff the XD flag is set in at least one of
/// those structures.
///
/// In practice, we always set these flags to their more permissive state in directories and only
/// make more restrictive settings in the frame mappings. (Ensured in the invariant, see conjunct
/// `directories_have_flags` in refinement layers 1 and 2.) But in the hardware model we still
/// define the full, correct semantics to ensure the implementation sets the flags correctly.
///
/// Note that `valid_pt_walk` is only true for the base address of a mapping. E.g. if a 4k entry is
/// mapped at address 0, then we have `valid_pt_walk(.., 0, ..)` but not `valid_pt_walk(.., 1, ..)`.
pub open spec fn valid_pt_walk(
    pt_mem: mem::PageTableMemory,
    addr: usize,
    pte: PTE,
) -> bool {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    let l2_idx: nat = l2_bits!(addr) as nat;
    let l3_idx: nat = l3_bits!(addr) as nat;
    match read_entry(pt_mem, pt_mem.cr3_spec()@.base, 0, l0_idx) {
        GPDE::Directory { addr: dir_addr, RW: l0_RW, US: l0_US, XD: l0_XD, .. } => {
            match read_entry(pt_mem, dir_addr as nat, 1, l1_idx) {
                GPDE::Page { addr: page_addr, RW: l1_RW, US: l1_US, XD: l1_XD, .. } => {
                    aligned(addr as nat, L1_ENTRY_SIZE as nat) && pte == PTE {
                        frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                        flags: Flags {
                            is_writable: l0_RW && l1_RW,
                            is_supervisor: !l0_US || !l1_US,
                            disable_execute: l0_XD || l1_XD,
                        },
                    }
                },
                GPDE::Directory { addr: dir_addr, RW: l1_RW, US: l1_US, XD: l1_XD, .. } => {
                    match read_entry(pt_mem, dir_addr as nat, 2, l2_idx) {
                        GPDE::Page { addr: page_addr, RW: l2_RW, US: l2_US, XD: l2_XD, .. } => {
                            aligned(addr as nat, L2_ENTRY_SIZE as nat) && pte == PTE {
                                frame: MemRegion {
                                    base: page_addr as nat,
                                    size: L2_ENTRY_SIZE as nat,
                                },
                                flags: Flags {
                                    is_writable: l0_RW && l1_RW && l2_RW,
                                    is_supervisor: !l0_US || !l1_US || !l2_US,
                                    disable_execute: l0_XD || l1_XD || l2_XD,
                                },
                            }
                        },
                        GPDE::Directory { addr: dir_addr, RW: l2_RW, US: l2_US, XD: l2_XD, .. } => {
                            match read_entry(pt_mem, dir_addr as nat, 3, l3_idx) {
                                GPDE::Page { addr: page_addr, RW: l3_RW, US: l3_US, XD: l3_XD, .. } => {
                                    aligned(addr as nat, L3_ENTRY_SIZE as nat) && pte
                                        == PTE {
                                        frame: MemRegion {
                                            base: page_addr as nat,
                                            size: L3_ENTRY_SIZE as nat,
                                        },
                                        flags: Flags {
                                            is_writable: l0_RW && l1_RW && l2_RW && l3_RW,
                                            is_supervisor: !l0_US || !l1_US || !l2_US || !l3_US,
                                            disable_execute: l0_XD || l1_XD || l2_XD || l3_XD,
                                        },
                                    }
                                },
                                GPDE::Directory { .. } => false,
                                GPDE::Empty => false,
                            }
                        },
                        GPDE::Empty => false,
                    }
                },
                GPDE::Empty => false,
            }
        },
        _ => false,
    }
}

// Can't use `n as usize` in triggers because it's an arithmetic expression
pub open spec fn nat_to_usize(n: nat) -> usize
    recommends n <= usize::MAX,
{
    n as usize
}

/// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: pt_mem::PTMem) -> Map<nat, PTE> {
    // TODO:
    arbitrary()
    //Map::new(
    //    |addr: nat|
    //        addr
    //            < MAX_BASE
    //        // Casting addr to usize is okay since addr < MAX_BASE < usize::MAX
    //         && exists|pte: PTE| valid_pt_walk(pt_mem, nat_to_usize(addr), pte),
    //    |addr: nat| choose|pte: PTE| valid_pt_walk(pt_mem, nat_to_usize(addr), pte),
    //)
}

pub open spec fn init<M: mmu::MMU>(c: Constants, s: State<M>) -> bool {
    &&& c.node_count > 0
    &&& forall|id: nat| #[trigger] valid_node_id(c, id) == s.nodes.contains_key(id)
    &&& forall|id: nat| #[trigger] valid_node_id(c, id) ==> NUMA_init(c, s.nodes[id])
    &&& s.mmu.init()
}

pub open spec fn NUMA_init(c: Constants, n: PerNodeState) -> bool {
    &&& c.core_count > 0
    &&& forall|id: nat| #[trigger] valid_core_id(c, id) == n.cores.contains_key(id)
    &&& forall|id: nat| #[trigger] valid_core_id(c, id) ==> n.cores[id].tlb.dom() === Set::empty()
}

pub open spec fn step_MMUStep<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>, lbl: mmu::Lbl) -> bool {
    // TODO: Make barrier separate transition and include in map end
    &&& !(lbl is Walk || lbl is Invlpg)
    &&& M::next(s1.mmu, s2.mmu, lbl)

    &&& s2.mem === s1.mem
    &&& s2.nodes === s1.nodes
}

pub open spec fn step_Invlpg<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>, core: Core, addr: usize) -> bool {
    &&& M::next(s1.mmu, s2.mmu, mmu::Lbl::Invlpg(core, addr))

    &&& s2.mem === s1.mem
    &&& s2.nodes === s1.nodes
}

// We only allow aligned accesses. Can think of unaligned accesses as two aligned accesses. When we
// get to concurrency we may have to change that.
pub open spec fn step_ReadWrite<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    vaddr: nat,
    paddr: nat,
    op: HWRWOp,
    walk_result: WalkResult,
    core: Core,
) -> bool {
    &&& aligned(vaddr, 8)

    //page tables and TLBs stay the same
    &&& s2.nodes === s1.nodes
    &&& valid_core(c, core)
    // TODO: matching on the walk_result is a bit awkward here
    &&& match walk_result {
        WalkResult::Valid { vbase, pte } => {
            let pmem_idx = word_index_spec(paddr);
            &&& s2.mmu == s1.mmu
            // If we have a `Valid` walk result, it must be a TLB-cached mapping that maps vaddr to paddr..
            &&& s1.nodes[core.node_id].cores[core.core_id].tlb.contains_pair(vbase as nat, pte)
            &&& between(vaddr, vbase as nat, vbase as nat + pte.frame.size)
            &&& paddr === (pte.frame.base + (vaddr - vbase)) as nat
            // .. and the result depends on the flags.

            &&& match op {
                HWRWOp::Store { new_value, result } => {
                    if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor
                        && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === s1.mem.update(pmem_idx as int, new_value)
                    } else {
                        &&& result is Pagefault
                        &&& s2.mem === s1.mem
                    }
                },
                HWRWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor && (is_exec
                        ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem[pmem_idx as int]
                    } else {
                        &&& result is Pagefault
                    }
                },
            }
        },
        WalkResult::Invalid { vaddr: vaddr_r } => {
            &&& vaddr == vaddr_r
            &&& M::next(s1.mmu, s2.mmu, mmu::Lbl::Walk(core, walk_result))

            // .. and the result is always a page fault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& match op {
                HWRWOp::Store { new_value, result } => result is Pagefault,
                HWRWOp::Load { is_exec, result } => result is Pagefault,
            }
        },
    }
}

pub open spec fn other_nodes_and_cores_unchanged<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool
    recommends valid_core(c, core),
{
    //Memory stays the same
    &&& s2.mem === s1.mem
    //Number of Numa nodes stays the same
    //all NUMA states are the same besides the one of node_id

    &&& s2.nodes.dom() === s1.nodes.dom()
    &&& s2.nodes.remove(core.node_id) === s1.nodes.remove(core.node_id)
    //all cores_states of node_id stay the same besides core_id

    &&& s2.nodes[core.node_id].cores.dom() === s1.nodes[core.node_id].cores.dom()
    &&& s2.nodes[core.node_id].cores.remove(core.core_id) == s1.nodes[core.node_id].cores.remove(core.core_id)
}

pub open spec fn valid_node_id(c: Constants, id: nat) -> bool {
    id < c.node_count
}

pub open spec fn valid_core_id(c: Constants, id: nat) -> bool {
    id < c.core_count
}

pub open spec fn valid_core(c: Constants, core: Core) -> bool {
    &&& valid_node_id(c, core.node_id)
    &&& valid_core_id(c, core.core_id)
}

pub open spec fn step_TLBFill<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
    vbase: usize,
    pte: PTE,
) -> bool {
    &&& valid_core(c, core)
    &&& M::next(s1.mmu, s2.mmu, mmu::Lbl::Walk(core, WalkResult::Valid { vbase, pte }))
    &&& s2.nodes[core.node_id].cores[core.core_id].tlb
        == s1.nodes[core.node_id].cores[core.core_id].tlb.insert(vbase as nat, pte)
    &&& other_nodes_and_cores_unchanged(c, s1, s2, core)
}

pub open spec fn step_TLBEvict<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    vaddr: nat,
    core: Core,
) -> bool {
    &&& valid_core(c, core)
    &&& s1.nodes[core.node_id].cores[core.core_id].tlb.contains_key(vaddr)
    &&& s2.nodes[core.node_id].cores[core.core_id].tlb
        === s1.nodes[core.node_id].cores[core.core_id].tlb.remove(vaddr)
    &&& other_nodes_and_cores_unchanged(c, s1, s2, core)
    &&& s2.mmu == s1.mmu
}

pub open spec fn step_Stutter<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>) -> bool {
    &&& s2 == s1
}

pub open spec fn next_step<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>, step: Step) -> bool {
    match step {
        Step::Invlpg { core, vaddr }       => step_Invlpg(c, s1, s2, core, vaddr),
        Step::Stutter                      => step_Stutter(c, s1, s2),
        Step::ReadWrite { vaddr, paddr, op, walk_result, core }
                                           => step_ReadWrite(c, s1, s2, vaddr, paddr, op, walk_result, core),
        Step::MMUStep { lbl }              => step_MMUStep(c, s1, s2, lbl),
        Step::TLBFill { vaddr, pte, core } => step_TLBFill(c, s1, s2, core, vaddr, pte),
        Step::TLBEvict { vaddr, core }     => step_TLBEvict(c, s1, s2, vaddr, core),
    }
}

pub open spec fn next<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>) -> bool {
    exists|step: Step| next_step(c, s1, s2, step)
}

// pub closed spec fn inv(s: State) -> bool {
//     true
// }
//
// proof fn init_implies_inv(s: State)
//     requires
//         init(s),
//     ensures
//         inv(s)
// { }
//
// proof fn next_preserves_inv(s1: State, s2: State)
//     requires
//         next(s1, s2),
//         inv(s1),
//     ensures
//         inv(s2),
// {
//     let step = choose|step: Step| next_step(s1, s2, step);
//     match step {
//         Step::ReadWrite { vaddr, paddr, op , pte} => (),
//         Step::PTWrite                             => (),
//         Step::TLBFill  { vaddr, pte }             => (),
//         Step::TLBEvict { vaddr }                  => (),
//     }
// }
} // verus!
