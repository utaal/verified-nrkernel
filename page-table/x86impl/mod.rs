#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
#[macro_use]
use crate::pervasive::*;

//pub mod page_table;
pub mod paging;

use paging::*;

#[macro_export]
macro_rules! bit {
    ($x:expr) => {
        1 << $x
    };
}

pub enum KError {
    BadAddress,
    GlobalMemoryNotSet,
    CoreAlreadyAllocated,
    OutOfMemory,
    ReplicaNotSet,
    ProcessNotSet,
    NotSupported,
    OutOfPids,
    NoExecutorForCore,
    NotMapped,
}

pub struct TlbFlushHandle {
    pub vaddr: VAddr,
    pub frame: Frame,
}

pub struct Frame {
    pub base: PAddr,
    pub size: usize,
    pub affinity: usize,
}

impl Frame {
    pub const fn const_new(base: PAddr, size: usize, node: usize) -> Frame {
        Frame {
            base,
            size,
            affinity: node,
        }
    }

    /// Create a new Frame given a PAddr range (from, to)
    pub fn from_range(range: (PAddr, PAddr), node: usize) -> Frame {
        //assert_eq!(range.0 % BASE_PAGE_SIZE, 0);
        //assert_eq!(range.1 % BASE_PAGE_SIZE, 0);
        //assert!(range.0 < range.1);

        requires([range.0 .0 < range.1 .0]);
        Frame {
            base: range.0,
            size: (range.1 .0 - range.0 .0) as usize,
            affinity: node,
        }
    }

    /// Make a new Frame at `base` with `size` with affinity `node`.
    pub fn new(base: PAddr, size: usize, node: usize) -> Frame {
        //assert_eq!(base.0 % BASE_PAGE_SIZE, 0);
        //assert_eq!(size % BASE_PAGE_SIZE, 0);

        Frame {
            base,
            size,
            affinity: node,
        }
    }

    /// Construct an empty, zero-length Frame.
    pub const fn empty() -> Frame {
        Frame {
            base: PAddr::zero(),
            size: 0,
            affinity: 0,
        }
    }

    fn zero(&mut self) {
        //unreachable!()
    }
}

/// Mapping rights to give to address translation.
#[derive(PartialEq, Eq, Copy, Clone)]
#[allow(unused)]
pub enum MapAction {
    /// Don't map
    None,
    /// Map region read-only.
    ReadUser,
    /// Map region read-only for kernel.
    ReadKernel,
    /// Map region read-write.
    ReadWriteUser,
    /// Map region read-write, disable page-cache for IO regions.
    ReadWriteUserNoCache,
    /// Map region read-write for kernel.
    ReadWriteKernel,
    /// Map region read-executable.
    ReadExecuteUser,
    /// Map region read-executable for kernel.
    ReadExecuteKernel,
    /// Map region read-write-executable.
    ReadWriteExecuteUser,
    /// Map region read-write-executable for kernel.
    ReadWriteExecuteKernel,
}

impl MapAction {
    /// Transform MapAction into rights for 1 GiB page.
    // TODO(Verus): why spec
    #[spec]
    pub fn to_pdpt_rights(self) -> u64 {
        match self {
            MapAction::None => 0x0,
            MapAction::ReadUser => PDPT_XD | PDPT_US,
            MapAction::ReadKernel => PDPT_XD,
            MapAction::ReadWriteUser => PDPT_RW | PDPT_XD | PDPT_US,
            MapAction::ReadWriteUserNoCache => PDPT_RW | PDPT_XD | PDPT_US,
            MapAction::ReadWriteKernel => PDPT_RW | PDPT_XD,
            MapAction::ReadExecuteUser => PDPT_US,
            MapAction::ReadExecuteKernel => 0x0,
            MapAction::ReadWriteExecuteUser => PDPT_RW | PDPT_US,
            MapAction::ReadWriteExecuteKernel => PDPT_RW,
        }
    }

    pub fn is_readable(&self) -> bool {
        //*self != MapAction::None
        // TODO(verus+needsfix):
        false
    }

    pub fn is_writable(&self) -> bool {
        // TODO(verus+needsfix):
        /*matches!(
            self,
            MapAction::ReadWriteUser
                | MapAction::ReadWriteUserNoCache
                | MapAction::ReadWriteKernel
                | MapAction::ReadWriteExecuteUser
                | MapAction::ReadWriteExecuteKernel
        )*/
        false
    }

    pub fn is_executable(&self) -> bool {
        // TODO(verus+needsfix):
        /*matches!(
            self,
            MapAction::ReadExecuteUser
                | MapAction::ReadExecuteKernel
                | MapAction::ReadWriteExecuteUser
                | MapAction::ReadWriteExecuteKernel
        )*/
        false
    }

    /// Transform MapAction into rights for 2 MiB page.
    // TODO(Verus): why spec
    #[spec]
    pub fn to_pd_rights(self) -> u64 {
        match self {
            MapAction::None => 0x0,
            MapAction::ReadUser => PD_XD | PD_US,
            MapAction::ReadKernel => PD_XD,
            MapAction::ReadWriteUser => PD_RW | PD_XD | PD_US,
            MapAction::ReadWriteUserNoCache => PD_RW | PD_XD | PD_US,
            MapAction::ReadWriteKernel => PD_RW | PD_XD,
            MapAction::ReadExecuteUser => PD_US,
            MapAction::ReadExecuteKernel => 0x0,
            MapAction::ReadWriteExecuteUser => PD_RW | PD_US,
            MapAction::ReadWriteExecuteKernel => PD_RW,
        }
    }

    /// Transform MapAction into rights for 4KiB page.
    // TODO(Verus): why spec
    #[spec]
    pub fn to_pt_rights(self) -> u64 {
        match self {
            MapAction::None => 0x0,
            MapAction::ReadUser => PT_XD | PT_US,
            MapAction::ReadKernel => PT_XD,
            MapAction::ReadWriteUser => PT_RW | PT_XD | PT_US,
            MapAction::ReadWriteUserNoCache => PT_RW | PT_XD | PT_US,
            MapAction::ReadWriteKernel => PT_RW | PT_XD,
            MapAction::ReadExecuteUser => PT_US,
            MapAction::ReadExecuteKernel => 0x0,
            MapAction::ReadWriteExecuteUser => PT_RW | PT_US,
            MapAction::ReadWriteExecuteKernel => PT_RW,
        }
    }
}

//use crate::memory::detmem::DA;
//use crate::memory::vspace::*;
//use crate::memory::{kernel_vaddr_to_paddr, paddr_to_kernel_vaddr, Frame, PAddr, VAddr};

fn paddr_to_kernel_vaddr(pa: PAddr) -> VAddr {
    // TODO(verusquestion): pa.inv() not working?
    requires([pa.0 < MAXPHYADDR]);

    VAddr::new(pa.0)
}

fn kernel_vaddr_to_paddr(va: VAddr) -> PAddr {
    // TODO(verusquestion): pa.inv() not working?
    // TODO we probably want to return Option<PAddr> here when we capture the fact that MAXVADDR > MAXPADDR
    // (hey we found a bug yay)
    requires([va.0 < MAXPHYADDR]);

    PAddr::new(va.0)
}
