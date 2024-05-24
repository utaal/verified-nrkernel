// Replicated Counter Example with Verified NR
// SPDX-License-Identifier: Apache-2.0 OR MIT

// trustedness: ignore this file

// stdlib dependencies
//use  std::sync::Arc;

// the verus dependencies
//use builtin::Tracked;

// the traits and types we need from the verified-node-replicaton crate
use crate::{/*AffinityFn,*/ Dispatch, /*NodeReplicated,*/ /*NodeReplicatedT, ThreadToken, SimpleLog*/};

use vstd::prelude::*;

verus! {

///// the number of replicas we want to create
//const NUM_REPLICAS: usize = 2;
//
///// number of operations each trhead executes
//const NUM_OPS_PER_THREAD: usize = 1_000_000;
//
///// number of threads per replica
//const NUM_THREADS_PER_REPLICA: usize = 4;
//
///// total number of threads being created
//const NUM_THREADS: usize = NUM_THREADS_PER_REPLICA*NUM_REPLICAS;


////////////////////////////////////////////////////////////////////////////////////////////////////
// Data Structure Definition with the Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a update operation on the data structure
/// the only possible operation is to increment a counter by two
#[derive(Clone, Copy)]
pub struct IncTwo(pub usize);

/// represents a read-only operation on the data structure
/// the only possible operation is to read a counter's value
pub struct Read(pub usize);

/// represents an operation request for either a read-only or update operation
pub enum OpRequest {
    /// this operation is mutating the data structure
    Update(IncTwo),
    /// this operation is read-only
    Readonly(Read),
}

/// represents the result of the operation request
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum OpResult {
    Value(u64),
    Ok,
    Err,
}

#[verifier(external_body)]
pub struct Counter { }

impl Counter {
    pub spec fn view(self) -> Seq<u64>;

    #[verifier(external_body)]
    pub fn new(i: usize) -> (res: Self)
        ensures
            res@.len() == i,
            forall|j: usize| j < i ==> res@[j as int] == 0
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub fn read(&self, i: usize) -> (res: u64)
        requires i < self@.len()
        ensures res == self@[i as int]
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub fn increment(&mut self, i: usize)
        requires i < old(self)@.len()
        ensures
            self@ == old(self)@.update(i as int, if old(self)@[i as int] < 0xffff_ffff_ffff_ffff {
                add(old(self)@[i as int], 1)
            } else { 0 })
    {
        unimplemented!()
    }
}


/// a simple counter data structure to be wrapped with node-replication
pub struct DataStructureType {
    pub num_counters: usize,
    pub counter: Counter,
}

impl DataStructureType {
    pub open spec fn view(self) -> Seq<u64> {
        self.counter@
    }

    pub open spec fn inv(&self) -> bool {
        self.num_counters == self@.len()
    }

    pub fn init(i: usize) -> (res: Self)
        ensures
            res@.len() == i,
            res.num_counters == i,
            forall|j: usize| j < i ==> res@[j as int] == 0,
            res.inv(),
    {
        DataStructureType {
            num_counters: i,
            counter: Counter::new(i),
        }
    }

    pub fn update(&mut self, op: IncTwo) -> (res: OpResult)
        requires old(self).inv()
        ensures
            self.inv(),
            self.num_counters == old(self).num_counters,
            if op.0 < self.num_counters {
                &&& self@ == old(self)@.update(op.0 as int,
                    if old(self)@[op.0 as int] == 0xffff_ffff_ffff_fffe { 0 }
                    else if old(self)@[op.0 as int] == 0xffff_ffff_ffff_ffff { 1 }
                    else { add(old(self)@[op.0 as int], 2) })
                    &&& res == OpResult::Ok
            } else {
                &&& self@ == old(self)@
                &&& res == OpResult::Err
            },
    {
        assert(self.num_counters == old(self)@.len());
        if op.0 < self.num_counters {
            self.counter.increment(op.0);
            self.counter.increment(op.0);
            assert(self@ == old(self)@.update(op.0 as int,
                    if old(self)@[op.0 as int] == 0xffff_ffff_ffff_fffe { 0 }
                    else if old(self)@[op.0 as int] == 0xffff_ffff_ffff_ffff { 1 }
                    else { add(old(self)@[op.0 as int], 2) }));
            OpResult::Ok
        } else {
            OpResult::Err
        }
    }

    pub fn read(&self, op: Read) -> (res: OpResult)
        requires self.inv()
        ensures
            if op.0 < self.num_counters {
                res == OpResult::Value(self@[op.0 as int])
            } else {
                res == OpResult::Err
            }
    {
        if op.0 < self.num_counters {
            OpResult::Value(self.counter.read(op.0))
        } else {
            OpResult::Err
        }
    }
}


/// implementation of Disatch for the Data Structure
impl Dispatch for DataStructureType {
    type ReadOperation = Read;

    type WriteOperation = IncTwo;

    type Response = OpResult;

    type View = Seq<u64>;

    open spec fn view(&self) -> Self::View {
        self.counter@
    }

    open spec fn inv(&self) -> bool {
        self.inv()
    }

    open spec fn init_spec() -> Self::View {
        seq![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    }

    open spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response {
        let i = op.0 as int;
        if i < ds.len() {
            OpResult::Value(ds[i])
        } else {
            OpResult::Err
        }
    }

    open spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (
        Self::View,
        Self::Response)
    {
        let i = op.0 as int;
        if i < ds.len() {
            (ds.update(i,
                       if ds[i] == 0xffff_ffff_ffff_fffe { 0 }
                       else if ds[i] == 0xffff_ffff_ffff_ffff { 1 }
                       else { add(ds[i], 2) }),
             OpResult::Ok)
        } else {
            (ds, OpResult::Err)
        }
    }

    fn init() -> Self {
        // TODO(MB): Can i not have an argument in this init function?
        let s = DataStructureType::init(10);
        assert(s@ =~= DataStructureType::init_spec());
        s
    }

    #[verifier::external_body]
    fn clone_write_op(op: &Self::WriteOperation) -> Self::WriteOperation {
        op.clone()
    }

    #[verifier::external_body]
    fn clone_response(op: &Self::Response) -> Self::Response {
        op.clone()
    }

    /// Method on the data structure that allows a read-only operation to be
    /// executed against it.
    fn dispatch(&self, op: Self::ReadOperation) -> Self::Response {
        self.read(op)
    }

    /// Method on the data structure that allows a write operation to be
    /// executed against it.
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> Self::Response {
        let res = self.update(op);
        proof {
            if (op.0 as int) < old(self)@.len() { } else { }
        }
        res
    }
}


//proof fn foo() {
//    //SimpleLog::State<DataStructureType>.log;
//    //let init = SimpleLog::initalize();
//    let x = SimpleLog::Step::<DataStructureType>::readonly_start(arbitrary(), arbitrary());
//    let s: bool = SimpleLog::State::<DataStructureType>::initialize(arbitrary());
//    //s.nrstate_at_version(0)
//}

//struct NrCounter(Arc<NodeReplicated<DataStructureType>>, ThreadToken<DataStructureType>);


////////////////////////////////////////////////////////////////////////////////////////////////////
// Data Structure Definition with the Operations
////////////////////////////////////////////////////////////////////////////////////////////////////


//pub fn main() {
//
//    println!("Creating Replicated Data Structure...");
//
//    let affinity_fn = AffinityFn::new(|f| {});
//
//    let mut nr_counter = NodeReplicated::new(NUM_REPLICAS, affinity_fn);
//
//    println!("Obtaining Thread tokens for {NUM_THREADS} threads...");
//
//    let mut thread_tokens = Vec::with_capacity(NUM_THREADS);
//    for idx in 0..NUM_THREADS+2*NUM_REPLICAS {
//        if let Option::Some(tkn) = nr_counter.register(idx % NUM_REPLICAS) {
//            println!(" - thread: {}.{}", tkn.replica_id(), tkn.thread_id());
//            thread_tokens.push(tkn);
//        } else {
//            panic!("could not register with replica!");
//        }
//    }
//
//    let nr_counter = Arc::new(nr_counter);
//
//    // The replica executes a Modify or Access operations by calling
//    // `execute_mut` and `execute`. Eventually they end up in the `Dispatch` trait.
//    let thread_loop = |counter: NrCounter| {
//        let NrCounter(counter, mut tkn) = counter;
//        let tid = (tkn.replica_id(), tkn.thread_id());
//        println!("Thread #{tid:?} start. executing {NUM_OPS_PER_THREAD} operations");
//        let mut num_updates = 0;
//        for i in 0..NUM_OPS_PER_THREAD {
//            match (tid.1 as usize + i) % 2 {
//                0 => {
//                    // println!(" - Thread #{tid:?}  executing Update operation {i}");
//                    num_updates += 1;
//                    match counter.execute_mut(IncTwo::IncEven, tkn, Tracked::assume_new()) {
//                        Result::Ok((ret, t, _)) => {
//                            tkn = t;
//                        },
//                        Result::Err((t, _)) => {
//                            tkn = t;
//                        }
//                    }
//                }
//                _ => {
//                    // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
//                    match  counter.execute(Read::Get, tkn, Tracked::assume_new()) {
//                        Result::Ok((ret, t, _)) => {
//                            tkn = t;
//                        },
//                        Result::Err((t, _)) => {
//                            tkn = t;
//                        }
//                    }
//                }
//            };
//
//            // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
//            match  counter.execute(Read::Get, tkn, Tracked::assume_new()) {
//                Result::Ok((ret, t, _)) => {
//                    tkn = t;
//                },
//                Result::Err((t, _)) => {
//                    tkn = t;
//                }
//            }
//        }
//
//        // make sure to make progress on all replicas
//        for _ in 0..NUM_OPS_PER_THREAD*2  {
//            std::thread::yield_now();
//            match counter.execute(Read::Get, tkn, Tracked::assume_new()) {
//                Result::Ok((ret, t, _)) => {
//                    tkn = t;
//                },
//                Result::Err((t, _)) => {
//                    tkn = t;
//                }
//            }
//        }
//        println!("Thread #{tid:?} done. executed {num_updates} update operations");
//    };
//
//    println!("Creating {NUM_THREADS} threads...");
//
//    let mut threads = Vec::with_capacity(NUM_THREADS);
//    for idx in 0..NUM_THREADS {
//        let counter = nr_counter.clone();
//        let tkn = thread_tokens.pop().unwrap();
//        threads.push(std::thread::spawn(move || {
//            thread_loop(NrCounter(counter, tkn));
//        }));
//    }
//
//    println!("Waiting for threads to finish...");
//
//    // Wait for all the threads to finish
//    for idx in 0..NUM_THREADS {
//        let thread = threads.pop().unwrap();
//        thread.join().unwrap();
//    }
//
//    println!("Obtain final result...");
//
//    for idx in 0..NUM_REPLICAS {
//        let tkn = thread_tokens.pop().unwrap();
//        match nr_counter.execute(Read::Get, tkn, Tracked::assume_new()) {
//            Result::Ok((ret, t, _)) => {
//                match ret {
//                    OpResult::Value(v) => {
//                        println!("Replica {idx} - Final Result: {v} expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
//                    }
//                    OpResult::Ok => {
//                        println!("Replica {idx} - Final Result: OK? expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
//                    }
//                }
//            },
//            Result::Err(t) => {
//                println!("Replica {idx} - Final Result: Err");
//            }
//        }
//    }
//
//    println!("Done!");
//}

} // verus!
