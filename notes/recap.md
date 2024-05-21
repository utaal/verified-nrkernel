# Recap: HL design choices  & process

## Atomic or Split Transitions?

> ***_Spoiler:_*** The Answer is yes

### Atomic transitions

#### Why?

- Maps and Unmaps (and Resolve) are SystemCalls and should therefore be blocking other threads in a Numa_node and between Numa_nodes they are linearized. Therefore it makes sense to make these Guarantees.

- (nonsynchronous accesses by the mmu during Maps and Unmaps might or might not sucseed however those are programmers bugs.) 

- Modeling them atomic gives strong guarantees and a simlpe, sleek interface for Programms building on this.

#### How?

- Guaranteeing Atomic expressions means we dont have to explictly model threads:  
    
    - Since the view on vaddr only changes between Map and Unmap and those are atomic the view of vmem is the same 





### split transitions

#### Why?

- explicitely modelling threads gives us more confidence that we really model what 

- is closer to actual low-level view and might or might not be easier to refine (from/to? i still dont know what diretion it goes....) OS/Hardware state machine

#### How (loose overview of the design process)

1. ***_Approach_***
   - Following transitions should be split: Map, Unmap, Resolve
   - stutter dosnt make sense to split
   - ReadWriteMemop belong to Memory_model and is handled according to it -> see Future Work
   - Effect is guaranteed to be visible after end

2. ***_Implementation_***
   - A map is implemented to keep track of Thread_state and Arguments  
   (Andrea suggested using an Array bc of bad experiences with Daphne, 
   however Matthias reassured that verus does not have these problems)
   - We use an Enum for the Arguments/Thread_state
> ***_Annotation_*** Enabling Conditions should only be needed at transition start since a transition might be stuck otherwise, which not behaviour that we want to model

> ***_PROBLEM_*** Now two incoming maps could map the same physical memory, as pte is only visible after mapping is complete to other threads and no enabling condition at the end to stop such a mistake -> accidental aliasing

1. ***_Approach_***
   - track inflight memory. dont make guarantees about memops upon or other operations on them while they are inflight. -> See Undefined Typ II
   - we delete infilght memmory from mem_dom
   - we rename pagefault to undefined

> ***_PROBLEM_*** What we modeld so far is not what we wanted: the end conditions are semi-linearization points for the mappings.

-> We delete mapping in the beginning of unmap, since this function is the reversal of map.
- reads and writes might still work but result is undefined. (unmapped == inflight -> see  )
- we now also need to track physical memory (if existing) of unmap so that we dont map over 


> ***_Annotation_*** But how do we Handle vmem?

-> see undefinde type III

### Conclusion

We have L0 and L1 Higherlevel Specs and refine from one to the other. This gives us the best of both worlds.


## 3 Flavors of undefined

### 1. Results of reads from freshly mapped memory 
- (unless this Memory is being unmapped right now)
- see at Future Work/ zero'd memory 
### 2. Inflight Memory 

- Inflight Memory is being treated as unmapped memory. This mean performaning a read might result in a success or a pagefault; It's undefined.
- we take it out of our view of vmem as dont make any guarantees about it

#### This means we are not guaranteeing Pagefaults anymore. Why is this ok? 

- pagefaults are errorhandling. Programms that require errorhandling are Programms with errors. We dont wanna validate these. 
### 3. Multiple PageTable operation on same vaddr

We don't make any guaranteed about this behavior. it is undefined. (or modeling the endless possible outcomes gives little sense for much work. )
We in generall call this an programmers bug, as the programmer is actively data-racing vaddr. 

#### Approaches

1. Prevent it in the enabling condition, similair to  
    - less realistic. enabling condition should be smth actor can just on themself, There is no magical global atomic state.
    - Overlapping memory is a programmers bug. It's realistic to model that and not forbid it.
2. put on flags on Threads to invalidate operations
3. as soon as an operation realizes it overlapps put global state to arbitary() in order to prevent sensible proofs containing this behavior
   - ruins my wf proof :(
   - simplest, does the job

-> we use 3. so far. 

## Introducing wf

wf is a predicate of things that are always true (inherently by stucture) that you dont explicitly need to maintain about our State mashine. This is expressed by the wf predicate and a proof

### why?

- its somewhat of a standard to express wellformedness
- its cumbersome to explicitly check that the conditions at all transitions, when they just should be true independt on how we transition our statemachine
- its nice to have implicit propertees expressed explicitely and makes it easier for upper layers.
- TODO: ask why did we need finite again?

### how?

````
pub open spec fn wf(c: AbstractConstants, s:AbstractVariables) -> bool {
    &&& forall |id: nat| id <= c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
    &&& s.mem.dom().finite()
}
````
and Black magic 

## Resolations around Resolve

#### We might should yeet it. Why? 
Resolve is used internally and shouldnt be used in the userspace for security reasons. therefore it shouldnt be exposed in the HL Specs
#### Why is there in the first place?
For completeness. Even if userspace pagewalks are handled by the MMU, The Kernal should still be able to Resolve Pagewalks. And it should to that with functional correctness. Having the three big Pagetable functions there showcases that one can proof functional correctness in a feasable way in the first place. 

## Mapping Large Memory Sections

#### why?

- For performance reasons it should be 

#### How?
- The underlying implementation could be a copy-and-swap
- However the current specs should already allow this behaviour. probably because how PageTableEntry is defined
- TODO: maybe ask? 

## Future work 

Nice Features that would be cool to guarantee but introduce too much complexity too early on or they are just no important enough for now.

### Aliasing

- pain in the ass probably to realize, but desireable

### Variable Threadnumber

- could be realized by a set of threadnumbers instead of 0-Threadnumber

### Guaranteeing Zero'd Memory

- Right now we dont make any guarantees about the value of reads of freshly mapped memory besides them existing. 

- its a nice thing to do and should only make on line difference in the specs

- However the implementation about zeroing (large) memoryregions (after unmap?) could be difficult  

### Look into other memory models 

- so far we have read_write as atomic. This is a very simple memory model.
- on hardware level it probably shouldnt be atomic but we should be able to refine it that way
- it makes sense to force an ordering on HL beause op will be before or after shootdown on maps 
- Memory models can become arbitary complex

