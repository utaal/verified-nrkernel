// HashMap Benchmark for upstream NR
// Adapted from https://github.com/vmware/node-replication/blob/master/node-replication/benches/hashmap/main.rs
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Defines a hash-map that can be replicated.
#![allow(dead_code)]
use std::fmt::Debug;
use std::marker::Sync;
use std::time::Duration;

use logging::warn;
use rand::seq::SliceRandom;

use bench_utils::benchmark::*;
use bench_utils::mkbench::{self, DsInterface};
use bench_utils::topology::ThreadMapping;
use bench_utils::Operation;
use verus_nr::{Dispatch, NodeReplicated, NR};


/// The initial amount of entries all Hashmaps are initialized with
#[cfg(feature = "smokebench")]
pub const INITIAL_CAPACITY: usize = 1 << 22; // ~ 4M
#[cfg(not(feature = "smokebench"))]
pub const INITIAL_CAPACITY: usize = 1 << 26; // ~ 67M

// Biggest key in the hash-map
#[cfg(feature = "smokebench")]
pub const KEY_SPACE: usize = 5_000_000;
#[cfg(not(feature = "smokebench"))]
pub const KEY_SPACE: usize = 50_000_000;

// Key distribution for all hash-maps [uniform|skewed]
pub const UNIFORM: &'static str = "uniform";

// Number of operation for test-harness.
#[cfg(feature = "smokebench")]
pub const NOP: usize = 2_500_000;
#[cfg(not(feature = "smokebench"))]
pub const NOP: usize = 25_000_000;

/// Operations we can perform on the stack.
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum OpWr {
    /// Increment the Counter
    Inc
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum OpRd {
    /// Get the counter value
    Get,
}

/// Single-threaded implementation of the stack
///
/// We just use a vector.
#[derive(Debug, Clone)]
pub struct NrCounter {
    counter: u64,
}

impl NrCounter {
    pub fn inc(&mut self) -> u64 {
        self.counter += 1;
        self.counter
    }
    pub fn get(&self) -> u64 {
        self.counter
    }
}

impl Default for NrCounter {
    /// Return a dummy hash-map with `INITIAL_CAPACITY` elements.
    fn default() -> NrCounter {
        NrCounter::init()
    }
}

impl Dispatch for NrCounter {
    type ReadOperation = OpRd;
    type WriteOperation = OpWr;
    type Response = Result<u64, ()>;
    type View = NrCounter;

    fn init() ->  Self
    {
        NrCounter { counter: 0 }
    }

    // partial eq also add an exec operation
    fn clone_write_op(op: &Self::WriteOperation) -> Self::WriteOperation{
        op.clone()
    }

    fn clone_response(op: &Self::Response) -> Self::Response {
        op.clone()
    }

    fn dispatch(&self, op: Self::ReadOperation) -> Self::Response {
        match op {
            OpRd::Get => return Ok(self.get()),
        }
    }

    /// Implements how we execute operation from the log against our local stack
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> Self::Response {
        match op {
            OpWr::Inc => {
                Ok(self.inc())
            }
        }
    }
}

/// Generate a random sequence of operations
///
/// # Arguments
///  - `nop`: Number of operations to generate
///  - `write`: true will Put, false will generate Get sequences
///  - `span`: Maximum key
///  - `distribution`: Supported distribution 'uniform' or 'skewed'
pub fn generate_operations(
    nop: usize,
    write_ratio: usize,
) -> Vec<Operation<OpRd, OpWr>> {
    let mut ops = Vec::with_capacity(nop);

    let mut t_rng = rand::thread_rng();

    for idx in 0..nop {
        if idx % 100 < write_ratio {
            ops.push(Operation::WriteOperation(OpWr::Inc));
        } else {
            ops.push(Operation::ReadOperation(OpRd::Get));
        }
    }

    ops.shuffle(&mut t_rng);
    ops
}

/// Compare scale-out behaviour of synthetic data-structure.
fn counter_scale_out<R>(c: &mut TestHarness, name: &str, write_ratio: usize)
where
    R: DsInterface + Send + Sync + 'static,
    R::D: Send,
    R::D: Dispatch<ReadOperation = OpRd>,
    R::D: Dispatch<WriteOperation = OpWr>,
    <R::D as Dispatch>::WriteOperation: Send + Sync,
    <R::D as Dispatch>::ReadOperation: Send + Sync,
    <R::D as Dispatch>::Response: Sync + Send + Debug,
{
    let ops = generate_operations(NOP, write_ratio);
    let bench_name = format!("{}-scaleout-wr{}", name, write_ratio);

    mkbench::ScaleBenchBuilder::<R>::new(ops)
        // .thread_defaults()
        .threads(1)
        .threads(16)
        //.threads(73)
        //.threads(96)
        //.threads(192)
        .update_batch(1)
        .log_size(2 * 1024 * 1024)
        .replica_strategy(mkbench::ReplicaStrategy::One)
        .replica_strategy(mkbench::ReplicaStrategy::Socket)
        .thread_mapping(ThreadMapping::Interleave)
        .log_strategy(mkbench::LogStrategy::One)
        .configure(
            c,
            &bench_name,
            |_cid, tkn, replica, op, _batch_size| match op {
                Operation::ReadOperation(op) => {
                    match replica.execute(*op, tkn) {
                        Ok(r) => r.1,
                        Err(r) => r
                    }
                }
                Operation::WriteOperation(op) => {
                    match replica.execute_mut(*op, tkn) {
                        Ok(r) => r.1,
                        Err(r) => r
                    }
                }
            },
        );
}

fn main() {
    let _r = env_logger::try_init();
    if cfg!(feature = "smokebench") {
        warn!("Running with feature 'smokebench' may not get the desired results");
    }

    bench_utils::disable_dvfs();

    let mut harness = TestHarness::new(Duration::from_secs(30));

    let write_ratios = if cfg!(feature = "exhaustive") {
        vec![0, 10, 20, 40, 60, 80, 100]
    } else if cfg!(feature = "smokebench") {
        vec![10]
    } else {
        vec![0, 10, 100]
    };

    //hashmap_single_threaded(&mut harness);
    for write_ratio in write_ratios.into_iter() {
        counter_scale_out::<NodeReplicated<NrCounter>>(&mut harness, "vnr-counter", write_ratio);
    }
}