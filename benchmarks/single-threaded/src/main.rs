extern crate alloc;
pub mod nros_vmem;
use std::time::Instant;

use x86::bits64::paging;

fn benchmark_nros_vmem() {
    let mut vmem = nros_vmem::VSpace {
        pml4: Box::pin(
            [paging::PML4Entry::new(paging::PAddr::from(0u64), paging::PML4Flags::empty()); paging::PAGE_SIZE_ENTRIES],
        ),
        allocs: Vec::with_capacity(10240),
    };
    for i in 0..1_000_000 {
        vmem.map_generic(paging::VAddr::from_usize(i * 4096), (paging::PAddr::from(0u64), 4096), nros_vmem::MapAction::ReadWriteUser).expect("map failed");
    }
    let time_before = Instant::now();
    for i in 1_000_000..101_000_000 {
        vmem.map_generic(
            paging::VAddr::from_usize(i * 4096),
            (paging::PAddr::from(0u64), 4096),
            nros_vmem::MapAction::ReadWriteUser).expect("map failed");
    }
    let time = time_before.elapsed();
    println!("Time Base Map: {} ns", time.as_nanos() as f64 / 100_000_000.0);

    // unmap

    for i in 0..1_000_000 {
        vmem.unmap(paging::VAddr::from_usize(i * 4096)).expect("unmap failed");
    }
    let time_before = Instant::now();
    for i in 1_000_000..101_000_000 {
        vmem.unmap(paging::VAddr::from_usize(i * 4096)).expect("unmap failed");
    }
    let time = time_before.elapsed();
    println!("Time Base Unmap: {} ns", time.as_nanos() as f64 / 100_000_000.0);
}

fn alloc_page() -> usize {
    let ptr: *mut u8 = unsafe {
        alloc::alloc::alloc(core::alloc::Layout::from_size_align_unchecked(
            4096,
            4096,
        ))
    };
    ptr as usize
}

fn benchmark_verif_noreclaim() {
    let root_dir1: *mut u64 = unsafe {
        alloc::alloc::alloc(core::alloc::Layout::from_size_align_unchecked(
            4096,
            4096,
        )) as *mut u64
    };
    let mut mem = verif_pt::spec_t::mem::new_page_table_memory_wrapper(0 as *mut u64, root_dir1 as u64, Box::new(alloc_page), Box::new(&|_| ()));
    let pte = verif_pt::definitions_t::PageTableEntryExec {
        flags: verif_pt::definitions_t::Flags {
            disable_execute: false,
            is_writable: true,
            is_supervisor: false,
        },
        frame: verif_pt::definitions_t::MemRegionExec {
            base: 0,
            size: 4096,
        },
    };
    for i in 0..101_000_000 {
        verif_pt::impl_u::l2_impl::PT::map_frame(&mut mem, &mut builtin::Ghost::assume_new(), i * 4096, pte.clone()).expect("map failed");
    }

    for i in 0..1_000_000 {
        verif_pt::impl_u::l2_impl::PT::unmap_noreclaim(&mut mem, i * 4096).expect("unmap failed");
    }
     
    let time_before = Instant::now();
    for i in 1_000_000..101_000_000 {
        verif_pt::impl_u::l2_impl::PT::unmap_noreclaim(&mut mem, i * 4096).expect("unmap failed");
    }
    let time = time_before.elapsed();
    println!("Time Verified Unmap (no reclaim): {} ns", time.as_nanos() as f64 / 100_000_000.0);
}

fn benchmark_verif() {
    let root_dir1: *mut u64 = unsafe {
        alloc::alloc::alloc(core::alloc::Layout::from_size_align_unchecked(
            4096,
            4096,
        )) as *mut u64
    };
    let mut mem = verif_pt::spec_t::mem::new_page_table_memory_wrapper(0 as *mut u64, root_dir1 as u64, Box::new(alloc_page), Box::new(&|_| ()));
    let pte = verif_pt::definitions_t::PageTableEntryExec {
        flags: verif_pt::definitions_t::Flags {
            disable_execute: false,
            is_writable: true,
            is_supervisor: false,
        },
        frame: verif_pt::definitions_t::MemRegionExec {
            base: 0,
            size: 4096,
        },
    };
    for i in 0..1_000_000 {
        verif_pt::impl_u::l2_impl::PT::map_frame(&mut mem, &mut builtin::Ghost::assume_new(), i * 4096, pte.clone()).expect("map failed");
    }
    let time_before = Instant::now();
    for i in 1_000_000..101_000_000 {
        verif_pt::impl_u::l2_impl::PT::map_frame(&mut mem, &mut builtin::Ghost::assume_new(), i * 4096, pte.clone()).expect("map failed");
    }
    let time = time_before.elapsed();
    println!("Time Verified Map: {} ns", time.as_nanos() as f64 / 100_000_000.0);

    for i in 0..1_000_000 {
        verif_pt::impl_u::l2_impl::PT::unmap(&mut mem, &mut builtin::Ghost::assume_new(), i * 4096).expect("unmap failed");
    }
     
    let time_before = Instant::now();
    for i in 1_000_000..101_000_000 {
        verif_pt::impl_u::l2_impl::PT::unmap(&mut mem, &mut builtin::Ghost::assume_new(), i * 4096).expect("unmap failed");
    }
    let time = time_before.elapsed();
    println!("Time Verified Unmap: {} ns", time.as_nanos() as f64 / 100_000_000.0);
}

fn main() {
    benchmark_verif();
    benchmark_verif_noreclaim();
    benchmark_nros_vmem();
}
