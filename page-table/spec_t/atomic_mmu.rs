use vstd::prelude::*;

use crate::definitions_t::{
    PageTableEntry
};
use crate::spec_t::hardware::{
    Core, PageDirectoryEntry, GhostPageDirectoryEntry
};

verus! {


pub struct VA {
    /// The indices used to index each level of the page table, each index is less than 512
    pub idx: Seq<nat>,
    /// The offset (bottom 12 bits)
    pub offset: nat,
}

pub enum Lbl {
    Tau,
    Walk {
        core: Core,
        va: VA,
        result: Option<PageTableEntry>,
    },
    Invlpg {
        core: Core,
        va: VA,
    },
    MFence {
        core: Core,
    },
    MemWrite {
        core: Core,
        pa: usize,
        value: usize,
    },
    MemRead {
        core: Core,
        pa: usize,
        value: usize,
    },
}

// FIXME: PageTableMemory in mem.rs doesn't have a proper view, which used to be fine but now we
// need one. We'll have to adjust mem.rs to use `PTMemView` as the view and replace `valid_pt_walk`
// in hardware.rs with the one in here, defined on the memory view.
pub struct PTMemView {
    phys_mem_ref: usize,
    cr3: usize,
    mem: Seq<usize>,
}

impl PTMemView {
    // TODO: need to actually specify this
    pub open spec fn read(self, pa: usize) -> usize;
    pub open spec fn write(self, pa: usize, value: usize) -> Self;
    ///// Read value at physical address `pa + idx * WORD_SIZE`
    //spec fn read(self, pa: usize, idx: usize) -> usize {
    //    self.mem[word_index(pa) + idx]
    //}
}


/// Information about a particular write to the page table memory. Used to track the write history.
/// To determine whether the previous value was a valid mapping we need to know the layer
/// We record the old and new values as `GhostPageDirectoryEntry` because the interpretation
/// depends on the rest of the memory state in which the write was executed. (TODO: This assumes
/// all writes are to entries in the tree, which may not be true.)
pub struct PTWrite {
    /// Core that initiated the write
    pub core: Core,
    /// Address to which it wrote
    pub pa: usize,
    ///// Set to true if both:
    ///// - `pa` is an entry reachable from cr3, and
    ///// - the entry was valid
    ///// TODO: What if it's mapped in multiple places? (We probably want to at least assume that
    ///// it's only mapped in one layer.
    //pub prev_valid: bool,
    /// The old value, interpreted as page directory entry
    pub old: GhostPageDirectoryEntry,
    /// The new value, interpreted as page directory entry
    pub new: GhostPageDirectoryEntry,
    ///// The (index) prefixes at which this entry was/is mapped. (Should currently always be
    ///// singleton set in our case.) For both old and new value. (I.e. prefix is included if at
    ///// least one of the two is valid and reachable.
    ///// TODO: technically don't need this. Address is sufficient. But we may want to track prefixes
    ///// anyway?
    //pub prefixes: Set<Seq<nat>>,
}

pub struct State {
    pub mem: PTMemView,
    // History variables
    /// Set of currently relevant writes for determining result of reads and page walks.
    /// Can be cleared by fences and invlpg.
    pub writes: Set<PTWrite>,
}

//impl PTWrite {
//    /// Check if all of the sequences in `self.prefixes` are prefixes of idx.
//    pub open spec fn all_prefixes_match(self, idx: Seq<nat>) -> bool {
//        forall|p| #![auto] self.prefixes.contains(p) ==> idx.take(p.len() as int) == p
//    }
//
//    /// Check if any of the sequences in `self.prefixes` are prefixes of idx.
//    pub open spec fn any_prefixes_match(self, idx: Seq<nat>) -> bool {
//        exists|p| #![auto] self.prefixes.contains(p) && idx.take(p.len() as int) == p
//    }
//}

impl State {
    pub open spec fn all_writes_by_core(self, core: Core) -> bool {
        forall|w| #![auto] self.writes.contains(w) ==> w.core == core
    }

    pub open spec fn no_overlapping_writes(self, pa: usize) -> bool {
        forall|w| #![auto] self.writes.contains(w) ==> w.pa != pa
    }

    pub open spec fn is_mfence_sufficient(self, core: Core) -> bool {
        forall|w| #![auto] self.writes.contains(w) ==> w.core == core && !(w.old is Empty)
    }

    ///// This function determines -- based on the past writes in `self.writes` -- whether writing
    ///// `value` to `pa` preserves the deterministic semantics of future (atomic) page table walks.
    //pub open spec fn is_good_write(self, pa: usize, value: usize, layer: nat) -> bool {
    //    let cur_pde = PageDirectoryEntry { entry: self.mem.read(pa) as u64, layer: Ghost(layer) }@;
    //    let new_pde = PageDirectoryEntry { entry: value as u64, layer: Ghost(layer) }@;
    //    // If writing to a directory mapping ..
    //    &&& cur_pde is Directory ==> {
    //        // .. we're only allowed to invalidate it
    //        &&& new_pde is Empty
    //        // .. and only if all its entries are invalid.
    //        &&& forall|pa2| cur_pde->Directory_addr <= pa2 < cur_pde->Directory_addr + 512
    //            ==> PageDirectoryEntry { entry: self.mem.read(pa2) as u64, layer: Ghost(layer + 1) }@ is Empty
    //    }
    //    // The address we're writing to must not be a directory mapping we previously changed or
    //    // one of its entries.
    //    &&& forall|w| #![auto] self.writes.contains(w) && w.old is Directory
    //            ==> w.pa != pa && (pa < w.old->Directory_addr || pa > w.old->Directory_addr + 512)
    //}
}

/// Returns Some if the page walk is successful. The second tuple component is the address of the
/// entry for the page mapping.
pub open spec fn pt_walk(s: PTMemView, va: VA) -> Option<(PageTableEntry, usize)>;

pub open spec fn step_MemWrite(pre: State, post: State, lbl: Lbl) -> bool {
    let layer = arbitrary(); // TODO: figure out where to get this from (technically, it might even be ambiguous)
    &&& lbl matches Lbl::MemWrite { core, pa, value }

    &&& post.mem == pre.mem.write(pa, value)
    &&& post.writes == pre.writes.insert(PTWrite {
        core,
        pa,
        //prev_valid: !(PageDirectoryEntry { entry: pre.mem.read(pa) as u64, layer: Ghost(layer) }@ is Empty),
        old: PageDirectoryEntry { entry: pre.mem.read(pa) as u64, layer: Ghost(layer) }@,
        new: PageDirectoryEntry { entry: value as u64, layer: Ghost(layer) }@,
        //prefixes: arbitrary(), // TODO: prefix of old entry and/or prefix of new entry
    })
}

/// We guarantee that reads are consistent with memory when `writes` is empty or otherwise when the
/// read is initiated by the core that performed the writes.
pub open spec fn step_MemRead(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MemRead { core, pa, value }

    &&& (pre.writes.is_empty() || pre.all_writes_by_core(core))
            ==> value == pre.mem.read(pa)

    &&& post == pre
}

pub open spec fn step_Walk(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk { core, va, result }

    // TODO: no overlapping writes is too strong of a condition. E.g. if we map (4K, 4K) and to do
    // so we have to map an empty directory [0, 2M], then our writes are affecting page table walks
    // at [0,4K] and [8K, 2M] as well.

    //&&& pre.deterministic_walk() ==> if let Some((pte, pg_entry_addr)) = pt_walk(pre.mem, va) {
    //    pre.no_overlapping_writes(pg_entry_addr) ==> result == Some(pte)
    //} else {
    //    result === None
    //}
    //&&& pre.no_overlapping_writes(va) ==> result == arbitrary::<Option<PageTableEntry>>() // TODO: atomic walk semantics
    //&&& !pre.bad ==> pte == {
    //    let cr3 = pre.pt_mem.cr3();
    //    let l0e = pre.pt_mem.read(add(cr3, va.l0_idx()));
    //    if l0e.is_valid() {
    //        let l1e = pre.pt_mem.read(add(l0e.get_addr(), va.l1_idx()));
    //        if l1e.is_valid() {
    //            Some(l1e)
    //        } else {
    //            None
    //        }
    //    } else {
    //        None
    //    }
    //}
    //
    &&& post == pre
}

/// If we didn't modify any valid entries, mfence can guarantee the absence of any subsequent stale
/// reads or walks.
/// TODO(MB): Should check if it's possible to just do this instead:
/// `post.writes == pre.writes.filter(|w:PTWrite| !(w.core == core && w.prev_valid))`
pub open spec fn step_MFence(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MFence { core }

    &&& post.mem == pre.mem
    &&& pre.is_mfence_sufficient(core) ==> post.writes === set![]
}

pub open spec fn step_Invlpg(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg { core, va }

    &&& post.mem == pre.mem
    &&& post.writes === if arbitrary() { set![] } else { pre.writes } // TODO:
}

pub open spec fn step_Stutter(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& post == pre
}

pub enum Step {
    MemWrite,
    MemRead,
    Walk,
    MFence,
    Invlpg,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::MemWrite => step_MemWrite(pre, post, lbl),
        Step::MemRead  => step_MemRead(pre, post, lbl),
        Step::Walk     => step_Walk(pre, post, lbl),
        Step::MFence   => step_MFence(pre, post, lbl),
        Step::Invlpg   => step_Invlpg(pre, post, lbl),
        Step::Stutter  => step_Stutter(pre, post, lbl),
    }
}

pub open spec fn init(pre: State) -> bool {
    &&& arbitrary()
}

pub open spec fn next(pre: State, post: State, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, step, lbl)
}

}
