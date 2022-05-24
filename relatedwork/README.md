# Related Work

Collection of related work and papers. 

TODO: we could put the actual appers here as well. 


## Machine Models

**Cassiopea**
 * ISA-models used to synthesize assembly programs
 * [Aquarium: Cassiopea and Alewife Languages](https://arxiv.org/abs/1908.00093)
 * [Cassiopea Tool](https://github.com/Harvard-PRINCESS/Cassiopea-Release)

**TLB Model**
 * This is the a model of a TLB in Isabelle/HOL from the seL4 folks. 
 * [Hira's PhD Thesis](https://hirataqdees.github.io/assets/img/phdthesis.pdf)
 * [Formal Reasoning Under Cached Address Translation](https://doi.org/10.1007/s10817-019-09539-7)
 * [Program Verification in the PResence of Cached Address Translation](https://hirataqdees.github.io/assets/img/itp18.pdf)
 * [Reasoning about Translation Lookaside Buffers](https://hirataqdees.github.io/assets/img/lpar17.pdf)
 * [Thread Modularity at Many Levels](https://dl.acm.org/doi/pdf/10.1145/3009837.3009893) Verifies TLB shootdowns in [Mach](https://dl.acm.org/doi/10.1145/68182.68193)

**Arm Memory Models**
 * This are the memory models from Peter Sewell's group in Cambridge
 * [Relaxed virtual memory in Armv8-A](https://link.springer.com/chapter/10.1007/978-3-030-99336-8_6)
 * [Related virtual memory in Armv8-A Website](https://www.cl.cam.ac.uk/~pes20/RelaxedVM-Arm/)
 * [A lot of papers by Sewell et al](https://www.cl.cam.ac.uk/~pes20/papers/topics.html#relaxed_all)
 * [Komodo ARM model in Dafny](https://github.com/microsoft/Komodo/blob/master/verified/ARMdef.s.dfy) Pretty detailed but models TLB in-validation with one boolean
 * [Verve](https://people.csail.mit.edu/jeanyang/papers/pldi117-yang.pdf) microkernel used for Ironclad apps

**Sail**
 * Sail is a langauge to express ISA semantics 
 * [Project website](https://www.cl.cam.ac.uk/~pes20/sail/)
