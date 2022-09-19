#![allow(unused_imports)]
use crate::pervasive::option::{*, Option::*};
use crate::pervasive::vec::*;
use crate::pervasive::result::{*, Result::*};

use crate::definitions_t::{ ArchExec, MemRegionExec, PageTableEntryExec, Flags, aligned_exec, MapResult, UnmapResult };
use crate::definitions_t::{ WORD_SIZE, PAGE_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAXPHYADDR_BITS };
use crate::mem_t as mem;

macro_rules! bit {
    ($v:expr) => {
        1u64 << $v
    }
}
// Generate bitmask where bits $low:$high are set to 1. (inclusive on both ends)
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0u64 << (($high+1u64)-$low))) << $low
    }
}

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table


// MASK_FLAG_* are flags valid for all entries.
pub const MASK_FLAG_P:    u64 = bit!(0u64);
pub const MASK_FLAG_RW:   u64 = bit!(1u64);
pub const MASK_FLAG_US:   u64 = bit!(2u64);
pub const MASK_FLAG_PWT:  u64 = bit!(3u64);
pub const MASK_FLAG_PCD:  u64 = bit!(4u64);
pub const MASK_FLAG_A:    u64 = bit!(5u64);
pub const MASK_FLAG_XD:   u64 = bit!(63u64);
// We can use the same address mask for all layers as long as we preserve the invariant that the
// lower bits that *should* be masked off are already zero.
pub const MASK_ADDR:      u64 = bitmask_inc!(12u64,MAXPHYADDR_BITS);
// const MASK_ADDR:      u64 = 0b0000000000001111111111111111111111111111111111111111000000000000;

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
pub const MASK_PG_FLAG_D:    u64 = bit!(6u64);
pub const MASK_PG_FLAG_G:    u64 = bit!(8u64);
pub const MASK_PG_FLAG_PAT:  u64 = bit!(12u64);

pub const MASK_L1_PG_FLAG_PS:   u64 = bit!(7u64);
pub const MASK_L2_PG_FLAG_PS:   u64 = bit!(7u64);

pub const MASK_L3_PG_FLAG_PAT:  u64 = bit!(7u64);

// const MASK_DIR_REFC:           u64 = bitmask_inc!(52u64,62u64); // Ignored bits for storing refcount in L3 and L2
// const MASK_DIR_L1_REFC:        u64 = bitmask_inc!(8u64,12u64); // Ignored bits for storing refcount in L1
// const MASK_DIR_REFC_SHIFT:     u64 = 52u64;
// const MASK_DIR_L1_REFC_SHIFT:  u64 = 8u64;
pub const MASK_DIR_ADDR:           u64 = MASK_ADDR;

// We should be able to always use the 12:52 mask and have the invariant state that in the
// other cases, the lower bits are already zero anyway.
pub const MASK_L1_PG_ADDR:      u64 = bitmask_inc!(30u64,MAXPHYADDR_BITS);
pub const MASK_L2_PG_ADDR:      u64 = bitmask_inc!(21u64,MAXPHYADDR_BITS);
pub const MASK_L3_PG_ADDR:      u64 = bitmask_inc!(12u64,MAXPHYADDR_BITS);


// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PageDirectoryEntry {
    pub entry: u64,
    // pub view: Ghost<GhostPageDirectoryEntry>,
    pub layer: (),
}

impl PageDirectoryEntry {

    pub fn new_page_entry(layer: usize, pte: PageTableEntryExec) -> Self
    {
        Self::new_entry(layer, pte.frame.base as u64, true, pte.flags.is_writable, pte.flags.is_supervisor, false, false, pte.flags.disable_execute)
    }

    pub fn new_dir_entry(layer: usize, address: u64) -> Self
    {
        // FIXME: check what flags we want here
        Self::new_entry(layer, address, false, true, true, false, false, false)
    }

    pub fn new_entry(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        ) -> PageDirectoryEntry
    {
        let e =
        PageDirectoryEntry {
            entry: {
                address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { MASK_FLAG_US }        else { 0 }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 }
            },
            layer: (),
        };
        e
    }

    pub fn address(&self) -> u64
    {
        self.entry & MASK_ADDR
    }

    pub fn is_mapping(&self) -> bool
    {
        (self.entry & MASK_FLAG_P) == MASK_FLAG_P
    }

    pub fn is_page(&self, layer: usize) -> bool
    {
        (layer == 3) || ((self.entry & MASK_L1_PG_FLAG_PS) == MASK_L1_PG_FLAG_PS)
    }

    pub fn is_dir(&self, layer: usize) -> bool
    {
        !self.is_page(layer)
    }
}

pub struct PageTable {
    pub memory: mem::PageTableMemory,
    pub arch: ArchExec,
    pub ghost_pt: (),
    // pub mem_structure: Ghost<Map<MemRegion,Seq<MemRegion>>>,
    // /// Reflexive, transitive closure of `mem_structure`
    // pub mem_rtrancl: Ghost<Map<MemRegion,Set<MemRegion>>>,
}

impl PageTable {
    /// Get the entry at address ptr + i * WORD_SIZE
    fn entry_at(&self, layer: usize, ptr: usize, i: usize, pt: ()) -> PageDirectoryEntry
    {
        PageDirectoryEntry {
            entry: self.memory.read(ptr + i * WORD_SIZE, ()),
            layer: (),
        }
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn resolve_aux(&self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: ()) -> Result<usize, ()>
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let entry      = self.entry_at(layer, ptr, idx, pt);
        if entry.is_mapping() {
            let entry_base: usize = self.arch.entry_base(layer, base, idx);
            if entry.is_dir(layer) {
                let dir_addr = entry.address() as usize;
                let res = self.resolve_aux(layer + 1, dir_addr, entry_base, vaddr, ());
                res
            } else {
                let offset: usize = vaddr - entry_base;
                let res = Ok(entry.address() as usize + offset);
                res
            }
        } else {
            Err(())
        }
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    pub fn resolve(&self, vaddr: usize) -> Result<usize,()>
    {
        let (cr3_region, cr3) = self.memory.cr3();
        let res = self.resolve_aux(0, cr3, 0, vaddr, ());
        res
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn map_frame_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, pte: PageTableEntryExec, pt: ())
        -> Result<(),()>
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let entry = self.entry_at(layer, ptr, idx, pt);
        let entry_base: usize = self.arch.entry_base(layer, base, idx);
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                if self.arch.entry_size(layer) == pte.frame.size {
                    Err(())
                } else {
                    let dir_addr = entry.address() as usize;
                    match self.map_frame_aux(layer + 1, dir_addr, entry_base, vaddr, pte, ()) {
                        Ok(rec_res) => {
                            Ok(())
                        },
                        Err(e) => {
                            Err(e)
                        },
                    }
                }
            } else {
                Err(())
            }
        } else {
            if self.arch.entry_size(layer) == pte.frame.size {
                let new_page_entry = PageDirectoryEntry::new_page_entry(layer, pte);
                let write_addr = ptr + idx * WORD_SIZE;
                self.memory.write(write_addr, (), new_page_entry.entry);

                Ok(())
            } else {
                let new_dir_region = self.memory.alloc_page();
                let new_dir_ptr = new_dir_region.base;
                let new_dir_ptr_u64 = new_dir_ptr as u64;
                let new_dir_entry = PageDirectoryEntry::new_dir_entry(layer, new_dir_ptr_u64);
                let write_addr = ptr + idx * WORD_SIZE;
                self.memory.write(write_addr, (), new_dir_entry.entry);


                match self.map_frame_aux(layer + 1, new_dir_ptr, entry_base, vaddr, pte, ()) {
                    Ok(rec_res) => {
                        Ok(())
                    },
                    Err(e) => {
                        Err(e)
                    },
                }
            }
        }
    }

    pub fn map_frame(&mut self, vaddr: usize, pte: PageTableEntryExec) -> MapResult
    {
        let (cr3_region, cr3) = self.memory.cr3();
        match self.map_frame_aux(0, cr3, 0, vaddr, pte, ()) {
            Ok(res) => {
                MapResult::Ok
            },
            Err(e) => {
                MapResult::ErrOverlap
            },
        }
    }

    fn is_directory_empty(&self, layer: usize, ptr: usize, pt: ()) -> bool
    {
        let mut idx = 0;
        let num_entries = self.arch.num_entries(layer);
        while idx < num_entries
        {
            // Any chance it's actually faster to just bitwise or all the entries together and check at the end?
            let entry = self.entry_at(layer, ptr, idx, pt);
            if entry.is_mapping() {
                return false;
            }
            idx = idx + 1;
        }
        true
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn unmap_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: ())
        -> Result<(),()>
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let entry = self.entry_at(layer, ptr, idx, pt);
        let entry_base: usize = self.arch.entry_base(layer, base, idx);
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                let dir_addr = entry.address() as usize;
                match self.unmap_aux(layer + 1, dir_addr, entry_base, vaddr, ()) {
                    Ok(rec_res) => {
                        if self.is_directory_empty(layer + 1, dir_addr, ()) {
                            let write_addr = ptr + idx * WORD_SIZE;
                            self.memory.write(write_addr, (), 0u64);
                            Ok(())
                        } else {
                            Ok(())
                        }
                    },
                    Err(e) => {
                        Err(e)
                    },
                }
            } else {
                if aligned_exec(vaddr, self.arch.entry_size(layer)) {
                    let write_addr = ptr + idx * WORD_SIZE;
                    self.memory.write(write_addr, (), 0u64);
                    Ok(())
                } else {
                    Err(())
                }
            }
        } else {
            Err(())
        }
    }

    // FIXME: need to do tlb invalidate
    pub fn unmap(&mut self, vaddr: usize) -> UnmapResult
    {
        let (cr3_region, cr3) = self.memory.cr3();
        match self.unmap_aux(0, cr3, 0, vaddr, ()) {
            Ok(res) => {
                UnmapResult::Ok
            },
            Err(e) => {
                UnmapResult::ErrNoSuchMapping
            },
        }
    }
}
