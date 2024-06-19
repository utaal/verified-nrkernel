// Replicated Counter Example with Verified NR
// SPDX-License-Identifier: Apache-2.0 OR MIT

// trustedness: ignore this file

// stdlib dependencies
use  std::sync::Arc;

// the verus dependencies
use builtin::Tracked;

// the traits and types we need from the verified-node-replicaton crate
use verified_node_replication::{AffinityFn, Dispatch, NodeReplicated, NodeReplicatedT, ThreadToken};

/// the number of replicas we want to create
const NUM_REPLICAS: usize = 2;

/// number of operations each trhead executes
const NUM_OPS_PER_THREAD: usize = 1_000_000;

/// number of threads per replica
const NUM_THREADS_PER_REPLICA: usize = 4;

/// total number of threads being created
const NUM_THREADS: usize = NUM_THREADS_PER_REPLICA*NUM_REPLICAS;


////////////////////////////////////////////////////////////////////////////////////////////////////
// Data Structure Definition with the Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// represents a update operation on the data structure
#[derive(Clone, Copy)]
pub enum UpdateOp {
    /// reset the counter to 0
    Reset,
    /// increment the counter
    Inc,
}

/// represents a read-only operation on the data structure
pub enum ReadonlyOp {
    /// get the current counter value
    Get,
}

/// represents an operation request for either a read-only or update operation
pub enum OpRequest {
    /// this operation is mutating the data structure
    Update(UpdateOp),
    /// this operation is read-only
    Readonly(ReadonlyOp),
}

/// represents the result of the operation request
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum OpResult {
    Value(u64),
    Ok,
}


/// a simple counter data structure to be wrapped with node-replication
pub struct DataStructureType {
    pub val: u64,
}

impl DataStructureType {
    pub fn init() -> Self
    {
        DataStructureType { val: 0 }
    }

    pub fn update(&mut self, op: UpdateOp) -> OpResult
    {
        match op {
            UpdateOp::Reset => self.val = 0,
            UpdateOp::Inc => self.val = if self.val < 0xffff_ffff_ffff_ffff { self.val + 1 } else { 0 }
        }
        OpResult::Ok
    }

    pub fn read(&self, op: ReadonlyOp) -> OpResult
    {
        OpResult::Value(self.val)
    }
}


/// implementation of Disatch for the Data Structure
impl Dispatch for DataStructureType {
    type ReadOperation = ReadonlyOp;

    type WriteOperation = UpdateOp;

    type Response = OpResult;

    type View = DataStructureType;

    // type View = DataStructureSpec;

    fn init() ->  Self
    {
        DataStructureType { val: 0 }
    }

    // partial eq also add an exec operation
    fn clone_write_op(op: &Self::WriteOperation) -> Self::WriteOperation{
        op.clone()
    }

    fn clone_response(op: &Self::Response) -> Self::Response {
        op.clone()
    }

    /// Method on the data structure that allows a read-only operation to be
    /// executed against it.
    fn dispatch(&self, op: Self::ReadOperation) -> Self::Response {
        match op {
            ReadonlyOp::Get => {
                OpResult::Value(self.val)
            }
        }
    }

    /// Method on the data structure that allows a write operation to be
    /// executed against it.
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> Self::Response {
        match op {
            UpdateOp::Reset => self.val = 0,
            UpdateOp::Inc => self.val = if self.val < 0xffff_ffff_ffff_ffff { self.val + 1 } else { 0 }
        }
        OpResult::Ok
    }
}





struct NrCounter(Arc<NodeReplicated<DataStructureType>>, ThreadToken<DataStructureType>);


////////////////////////////////////////////////////////////////////////////////////////////////////
// Data Structure Definition with the Operations
////////////////////////////////////////////////////////////////////////////////////////////////////


pub fn main() {

    println!("Creating Replicated Data Structure...");

    let affinity_fn = AffinityFn::new(|f| {});

    let mut nr_counter = NodeReplicated::new(NUM_REPLICAS, affinity_fn);

    println!("Obtaining Thread tokens for {NUM_THREADS} threads...");

    let mut thread_tokens = Vec::with_capacity(NUM_THREADS);
    for idx in 0..NUM_THREADS+2*NUM_REPLICAS {
        if let Option::Some(tkn) = nr_counter.register(idx % NUM_REPLICAS) {
            println!(" - thread: {}.{}", tkn.replica_id(), tkn.thread_id());
            thread_tokens.push(tkn);
        } else {
            panic!("could not register with replica!");
        }
    }

    let nr_counter = Arc::new(nr_counter);

    // The replica executes a Modify or Access operations by calling
    // `execute_mut` and `execute`. Eventually they end up in the `Dispatch` trait.
    let thread_loop = |counter: NrCounter| {
        let NrCounter(counter, mut tkn) = counter;
        let tid = (tkn.replica_id(), tkn.thread_id());
        println!("Thread #{tid:?} start. executing {NUM_OPS_PER_THREAD} operations");
        let mut num_updates = 0;
        for i in 0..NUM_OPS_PER_THREAD {
            match (tid.1 as usize + i) % 2 {
                0 => {
                    // println!(" - Thread #{tid:?}  executing Update operation {i}");
                    num_updates += 1;
                    match counter.execute_mut(UpdateOp::Inc, tkn, Tracked::assume_new()) {
                        Result::Ok((ret, t, _)) => {
                            tkn = t;
                        },
                        Result::Err((t, _)) => {
                            tkn = t;
                        }
                    }
                }
                _ => {
                    // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
                    match  counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
                        Result::Ok((ret, t, _)) => {
                            tkn = t;
                        },
                        Result::Err((t, _)) => {
                            tkn = t;
                        }
                    }
                }
            };

            // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
            match  counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
                Result::Ok((ret, t, _)) => {
                    tkn = t;
                },
                Result::Err((t, _)) => {
                    tkn = t;
                }
            }
        }

        // make sure to make progress on all replicas
        for _ in 0..NUM_OPS_PER_THREAD*2  {
            std::thread::yield_now();
            match counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
                Result::Ok((ret, t, _)) => {
                    tkn = t;
                },
                Result::Err((t, _)) => {
                    tkn = t;
                }
            }
        }
        println!("Thread #{tid:?} done. executed {num_updates} update operations");
    };

    println!("Creating {NUM_THREADS} threads...");

    let mut threads = Vec::with_capacity(NUM_THREADS);
    for idx in 0..NUM_THREADS {
        let counter = nr_counter.clone();
        let tkn = thread_tokens.pop().unwrap();
        threads.push(std::thread::spawn(move || {
            thread_loop(NrCounter(counter, tkn));
        }));
    }

    println!("Waiting for threads to finish...");

    // Wait for all the threads to finish
    for idx in 0..NUM_THREADS {
        let thread = threads.pop().unwrap();
        thread.join().unwrap();
    }

    println!("Obtain final result...");

    for idx in 0..NUM_REPLICAS {
        let tkn = thread_tokens.pop().unwrap();
        match nr_counter.execute(ReadonlyOp::Get, tkn, Tracked::assume_new()) {
            Result::Ok((ret, t, _)) => {
                match ret {
                    OpResult::Value(v) => {
                        println!("Replica {idx} - Final Result: {v} expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
                    }
                    OpResult::Ok => {
                        println!("Replica {idx} - Final Result: OK? expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
                    }
                }
            },
            Result::Err(t) => {
                println!("Replica {idx} - Final Result: Err");
            }
        }
    }

    println!("Done!");
}
