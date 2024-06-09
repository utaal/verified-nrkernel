#![verus::trusted]
use crate::definitions_t::{
    between, PageTableEntry, WORD_SIZE, above_zero, candidate_mapping_overlaps_existing_pmem, MemRegion, overlap
};
use crate::spec_t::mem;
use vstd::prelude::*;


use crate::extra::{lemma_set_of_first_n_nat_is_finite, lemma_subset_is_finite};

use crate::spec_t::hlspec::{mem_domain_from_entry, mem_domain_from_entry_contains, mem_domain_from_mappings, mem_domain_from_mappings_contains, inv, AbstractConstants, AbstractVariables, AbstractArguments, step_Unmap_start, mappings_frame_sizes_over_zero, pmem_no_overlap};



verus! {


//ensures that if a new mapping is added the old ones are still in there and no new other mappings appear
pub proof fn lemma_mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry,
)
    requires
        !mappings.dom().contains(base),
    ensures
        (forall|word_idx: nat|
            mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
                ==> #[trigger] mem_domain_from_mappings_contains(
                phys_mem_size,
                word_idx,
                mappings.insert(base, pte),
            )),
        (forall|word_idx: nat|
            !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
                && #[trigger] mem_domain_from_mappings_contains(
                phys_mem_size,
                word_idx,
                mappings.insert(base, pte),
            ) ==> between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size)),
{
    assert forall|word_idx: nat|
        mem_domain_from_mappings_contains(
            phys_mem_size,
            word_idx,
            mappings,
        ) implies #[trigger] mem_domain_from_mappings_contains(
        phys_mem_size,
        word_idx,
        mappings.insert(base, pte),
    ) by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base: nat, pte: PageTableEntry|
            {
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = mem::word_index_spec(paddr);
                &&& #[trigger] mappings.contains_pair(base, pte)
                &&& between(vaddr, base, base + pte.frame.size)
                &&& pmem_idx < phys_mem_size
            };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
    };
    assert forall|word_idx: nat|
        !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
            && #[trigger] mem_domain_from_mappings_contains(
            phys_mem_size,
            word_idx,
            mappings.insert(base, pte),
        ) implies between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size) by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base2: nat, pte2: PageTableEntry|
            {
                let paddr = (pte2.frame.base + (vaddr - base2)) as nat;
                let pmem_idx = mem::word_index_spec(paddr);
                &&& #[trigger] mappings.insert(base, pte).contains_pair(base2, pte2)
                &&& between(vaddr, base2, base2 + pte2.frame.size)
                &&& pmem_idx < phys_mem_size
            };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
        assert(between(vaddr, base2, base2 + pte2.frame.size));
        if !between(vaddr, base, base + pte.frame.size) {
            assert(base2 != base || pte2 !== pte);
            if base2 != base {
                assert(mappings.contains_pair(base2, pte2));
                assert(mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings));
            }
            assert(false);
        } else {
        }
    };


}

    
pub proof fn lemma_mem_domain_from_entry_finite(
    phys_mem_size: nat,
    base: nat,
    pte: PageTableEntry,
)
    requires
    ensures mem_domain_from_entry(phys_mem_size, base, pte).finite(),
{
    let bound = base + pte.frame.size;
    let vaddrs = mem_domain_from_entry(phys_mem_size, base, pte);
    let n_nats =  Set::new(|i: nat| i < (bound + 1 as nat));
    assert(vaddrs.subset_of(n_nats));
    lemma_set_of_first_n_nat_is_finite(bound + 1);
    lemma_subset_is_finite(n_nats, vaddrs);
    assert(vaddrs.finite());
}
    

pub proof fn lemma_mem_domain_from_empty_mappings_finite(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
)
    requires
         mappings.dom() === Set::empty(),
    ensures
         mem_domain_from_mappings(phys_mem_size, mappings).finite(),
{
    assert(mem_domain_from_mappings(phys_mem_size, mappings) === Set::empty())
}



pub proof fn lemma_mem_domain_from_mapping_finite (
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
)
    requires mappings.dom().finite(),
    ensures  mem_domain_from_mappings(phys_mem_size, mappings).finite(),
{
if (exists |bs: nat| mappings.dom().contains(bs)) {
        let  bs  = choose |bs: nat | mappings.dom().contains(bs);
        let pt = mappings[bs];
        let mappings_reduc = mappings.remove(bs);
        assert(!mappings_reduc.dom().contains(bs));
        assert(mappings_reduc.insert(bs,pt) == mappings);
        assert(mappings_reduc.dom().subset_of( mappings.dom() ));
        lemma_subset_is_finite(mappings.dom(), mappings_reduc.dom());
        lemma_mem_domain_from_mappings_finite_induction(
            phys_mem_size,
            mappings_reduc,
            bs,
            pt,
        );
    } else {
        assert(mappings.dom() === Set::empty());
        lemma_mem_domain_from_empty_mappings_finite(phys_mem_size, mappings);
    }
}



pub proof fn lemma_mem_domain_from_mappings_finite_induction (
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry, 
)
    requires mappings.dom().finite(),
            !mappings.dom().contains(base),
    ensures  mem_domain_from_mappings(phys_mem_size, mappings.insert(base, pte)).finite(),
    decreases mappings.dom().len(),
{
if (exists |bs: nat| mappings.dom().contains(bs)) {
        let  bs  = choose |bs: nat | mappings.dom().contains(bs);
        let pt = mappings[bs];
        let mappings_reduc = mappings.remove(bs);
        assert(!mappings_reduc.dom().contains(bs));
        assert(mappings_reduc.insert(bs,pt) == mappings);
        assert(mappings_reduc.dom().subset_of( mappings.dom() ));
        lemma_subset_is_finite(mappings.dom(), mappings_reduc.dom());
        lemma_mem_domain_from_mappings_finite_induction(
            phys_mem_size,
            mappings_reduc,
            bs,
            pt,
        );
    } else {
        assert(mappings.dom() === Set::empty());
        lemma_mem_domain_from_empty_mappings_finite(phys_mem_size, mappings);
    }
    lemma_finite_step(phys_mem_size, mappings, base, pte);
}


pub proof fn lemma_finite_step(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry, 
)
    requires mem_domain_from_mappings(phys_mem_size, mappings).finite(),
             mappings.dom().finite(),
            !mappings.dom().contains(base),
    ensures  mem_domain_from_mappings(phys_mem_size, mappings.insert(base, pte)).finite(),
{
    let mem_dom_ext = mem_domain_from_mappings(phys_mem_size, mappings.insert(base,pte));
    let mem_dom_union = mem_domain_from_mappings(phys_mem_size, mappings).union(mem_domain_from_entry(phys_mem_size, base, pte));
    assert forall |wrd : nat| mem_dom_ext.contains(wrd) implies mem_dom_union.contains(wrd) by {
    lemma_mem_domain_from_new_mappings_subset(phys_mem_size, mappings, base, pte, wrd);
    }
    assert(mem_dom_ext.subset_of(mem_dom_union));
    lemma_mem_domain_from_entry_finite(phys_mem_size, base, pte);
    assert(mem_dom_union.finite());
    lemma_subset_is_finite(mem_dom_union, mem_dom_ext);
}


pub proof fn lemma_mem_domain_from_new_mappings_subset(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    bs: nat,
    pt: PageTableEntry,
    word_idx: nat,
)
    requires
       mem_domain_from_mappings(phys_mem_size, mappings.insert(bs, pt)).contains(word_idx),
    ensures
       mem_domain_from_mappings(phys_mem_size, mappings).union(mem_domain_from_entry(phys_mem_size, bs, pt)).contains(word_idx)
        
{   
    let mappings_ext = mappings.insert(bs, pt);
    let vaddr = word_idx * WORD_SIZE as nat;
    let (base, pte) : (nat, PageTableEntry) = choose |base: nat, pte: PageTableEntry| {&&& #[trigger] mappings_ext.contains_pair(base, pte) 
                                                                                       &&& mem_domain_from_entry_contains( phys_mem_size, vaddr, base, pte,)};
    if (base === bs && pte === pt){
  
    assert(mem_domain_from_entry(phys_mem_size, bs, pt).contains(word_idx));
    
    } else {
    assert (mappings.contains_pair(base, pte));
    assert (mem_domain_from_mappings(phys_mem_size, mappings).contains(word_idx));

    }
        

}

pub proof fn lemma_overlap_sym(region1: MemRegion, region2: MemRegion)
    requires !overlap(region1, region2),
             region1.size > 0,
             region2.size > 0,
    ensures  !overlap(region2, region1),
     {
     
} 

pub proof fn lemma_overlap (mappings: Map<nat, PageTableEntry>, base: nat, pte : PageTableEntry)
    requires pmem_no_overlap(mappings),
            !candidate_mapping_overlaps_existing_pmem(mappings, pte),
            mappings_frame_sizes_over_zero(mappings),
            above_zero(pte.frame.size),
    ensures pmem_no_overlap(mappings.insert(base, pte)),
{   
    assert (forall |bs1: nat| #![auto] mappings.dom().contains(bs1) ==> !overlap( pte.frame, mappings.index(bs1).frame));
    assert forall |bs1: nat| #![auto] mappings.dom().contains(bs1) implies !overlap( mappings.index(bs1).frame, pte.frame) by {
        lemma_overlap_sym(pte.frame, mappings.index(bs1).frame);
    }
    assert(pmem_no_overlap(mappings.insert(base, pte)));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                               //
//                                        Step preserves inv proofs                                              //
//                                                                                                               //
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub proof fn unmap_start_preserves_inv(c: AbstractConstants, s1: AbstractVariables, s2:AbstractVariables, thread_id: nat, vaddr: nat)
    requires
        step_Unmap_start ( c, s1, s2, thread_id, vaddr ),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.dom().contains(thread_id),
    ensures
        s2.sound ==> inv(c, s2)
{
    if (s2.sound) {
        lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s1.mappings.remove(vaddr));
        assert(forall |id: nat| #![auto] s2.mappings.dom().contains(id) ==> s1.mappings.index(id) == s2.mappings.index(id));
        let pte = if (s1.mappings.dom().contains(vaddr)){Some (s1.mappings.index(vaddr))} else {Option::None};
        assert(s2.thread_state.values().subset_of(s1.thread_state.values().insert(AbstractArguments::Unmap{ vaddr, pte })));
    } else {}
}



}
