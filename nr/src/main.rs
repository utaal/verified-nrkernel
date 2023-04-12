// the verus dependencies
#[allow(unused_imports)]
use builtin::*;

use vstd::{
    option::Option,
    prelude::*,
    vec::Vec,
    *,
};

mod spec;
mod exec;
mod constants;

use constants::NUM_REPLICAS;

// spec imports
use crate::spec::types::*;

// exec imports
use crate::exec::context::ThreadToken;
use crate::exec::NodeReplicated;



use  std::sync::Arc;

struct NrCounter(Arc<NodeReplicated>, ThreadToken);

const NUM_OPS_PER_THREAD: usize = 1_000_000;
const NUM_THREADS_PER_REPLICA: usize = 4;
const NUM_THREADS: usize = NUM_THREADS_PER_REPLICA*NUM_REPLICAS;

// #[verifier(external_body)] /* vattr */
#[verifier::external_body] /* vattr */
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
                    match counter.execute_mut(UpdateOp::Inc, tkn) {
                        Result::Ok((ret, t)) => {
                            tkn = t;
                        },
                        Result::Err(t) => {
                            tkn = t;
                        }
                    }
                }
                _ => {
                    // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
                    match  counter.execute(ReadonlyOp::Get, tkn) {
                        Result::Ok((ret, t)) => {
                            tkn = t;
                        },
                        Result::Err(t) => {
                            tkn = t;
                        }
                    }
                }
            };

            // println!(" - Thread #{tid:?}  executing ReadOnly operation {i}");
            match  counter.execute(ReadonlyOp::Get, tkn) {
                Result::Ok((ret, t)) => {
                    tkn = t;
                },
                Result::Err(t) => {
                    tkn = t;
                }
            }
        }

        // make sure to make progress on all replicas
        for _ in 0..NUM_OPS_PER_THREAD*2  {
            std::thread::yield_now();
            match counter.execute(ReadonlyOp::Get, tkn) {
                Result::Ok((ret, t)) => {
                    tkn = t;
                },
                Result::Err(t) => {
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
        let tkn = thread_tokens.pop();
        threads.push(std::thread::spawn(move || {
            thread_loop(NrCounter(counter, tkn));
        }));
    }

    println!("Waiting for threads to finish...");

    // Wait for all the threads to finish
    for idx in 0..NUM_THREADS {
        let thread = threads.pop();
        thread.join().unwrap();
    }

    println!("Obtain final result...");

    for idx in 0..NUM_REPLICAS {
        let tkn = thread_tokens.pop();
        match nr_counter.execute(ReadonlyOp::Get, tkn) {
            Result::Ok((ret, t)) => {
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
