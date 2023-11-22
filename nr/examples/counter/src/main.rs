// the verus dependencies

// trustedness: ignore this file

use builtin::Tracked;

use verus_nr::{Dispatch, NR, NodeReplicated, ThreadToken};
use verus_nr::constants::NUM_REPLICAS;


/// represents a update operation on the replica, in NR this is handled by `dispatch_mut`
#[derive(Clone, Copy)]
pub enum UpdateOp {
    Reset,
    Inc,
}

/// Represents a read-only operation on the replica, in NR this is handled by `dispatch`
pub enum ReadonlyOp {
    Get,
}

/// the operations enum
pub enum Request {
    Update(UpdateOp),
    Readonly(ReadonlyOp),
}

/// Represents the return type of the read-only operation
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum ReturnType {
    Value(u64),
    Ok,
}



pub struct DataStructureType {
    pub val: u64,
}

impl DataStructureType {
    pub fn init() -> Self
    {
        DataStructureType { val: 0 }
    }

    pub fn update(&mut self, op: UpdateOp) -> ReturnType
    {
        match op {
            UpdateOp::Reset => self.val = 0,
            UpdateOp::Inc => self.val = if self.val < 0xffff_ffff_ffff_ffff { self.val + 1 } else { 0 }
        }
        ReturnType::Ok
    }

    pub fn read(&self, op: ReadonlyOp) -> ReturnType
    {
        ReturnType::Value(self.val)
    }
}

impl Dispatch for DataStructureType {
    type ReadOperation = ReadonlyOp;

    type WriteOperation = UpdateOp;

    type Response = ReturnType;

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
                ReturnType::Value(self.val)
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
        ReturnType::Ok
    }
}




use  std::sync::Arc;

struct NrCounter(Arc<NodeReplicated<DataStructureType>>, ThreadToken<DataStructureType>);

const NUM_OPS_PER_THREAD: usize = 1_000_000;
const NUM_THREADS_PER_REPLICA: usize = 4;
const NUM_THREADS: usize = NUM_THREADS_PER_REPLICA*NUM_REPLICAS;

pub fn main() {

    println!("Creating Replicated Data Structure...");

    let mut nr_counter = NodeReplicated::new(NUM_REPLICAS);

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
        }-- stay healthy!

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
                    ReturnType::Value(v) => {
                        println!("Replica {idx} - Final Result: {v} expected {}", NUM_THREADS * (NUM_OPS_PER_THREAD)/ 2);
                    }
                    ReturnType::Ok => {
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
