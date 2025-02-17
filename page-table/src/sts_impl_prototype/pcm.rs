use vstd::prelude::*;
use vstd::pcm::*;

verus!{

pub struct MemRegion {
    pub base: usize,
    pub size: usize,
}

pub open spec fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
    if region1.base <= region2.base {
        region1.base == region2.base || region2.base < region1.base + region1.size
    } else {
        region1.base < region2.base + region2.size
    }
}

pub struct RegPCM {
    pub regs: Set<MemRegion>,
}

impl PCM for RegPCM {
    open spec fn valid(self) -> bool {
        forall|s1, s2| self.regs.contains(s1) && self.regs.contains(s2) && s1 != s2 ==> !overlap(s1, s2)
    }

    open spec fn op(self, other: Self) -> Self {
        RegPCM { regs: self.regs.union(other.regs) }
    }

    open spec fn unit() -> Self {
        RegPCM { regs: set![] }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
        assert(a.regs.union(b.regs) =~= b.regs.union(a.regs));
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        assert(a.regs.union(b.regs.union(c.regs)) =~= a.regs.union(b.regs).union(c.regs));
    }

    proof fn op_unit(a: Self) {
        assert(a.regs.union(set![]) =~= a.regs);
    }

    proof fn unit_valid() {
    }
}



exec fn foo(n: usize, Tracked(regions): Tracked<&mut Resource<RegPCM>>) {

}

exec fn allocate_with_pcm(regions: Ghost<Set<MemRegion>>) -> (res: (MemRegion, Tracked<Resource<RegPCM>>)) {
    let reg = allocate(regions);
    let pcm = Ghost(RegPCM { regs: set![reg] });
    assert(pcm@.valid());
    let tracked resource = Resource::<RegPCM>::alloc(pcm@);
    (reg, Tracked(resource))
}


// Technically unsound/impossible to implement
#[verifier(external_body)]
exec fn allocate(regions: Ghost<Set<MemRegion>>) -> (res: MemRegion)
    ensures forall|r| regions@.contains(r) ==> !overlap(res, r)
{
    unimplemented!()
}




}
