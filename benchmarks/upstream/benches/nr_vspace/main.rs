// HashMap Benchmark for upstream NR
// Adapted from https://github.com/vmware/node-replication/blob/master/node-replication/benches/hashmap/main.rs
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Defines a hash-map that can be replicated.
#![allow(dead_code)]
// #![feature(generic_associated_types)]

use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::Sync;
use std::time::Duration;

use logging::warn;
use rand::seq::SliceRandom;
use rand::{distributions::Distribution, Rng, RngCore};
use rand_chacha::ChaCha8Rng;
use rand::SeedableRng;
use zipf::ZipfDistribution;

use bench_utils::benchmark::*;
use bench_utils::mkbench::{self, DsInterface, ThreadToken, NodeReplicated};
use bench_utils::topology::ThreadMapping;
use bench_utils::Operation;


// Number of operation for test-harness.
#[cfg(feature = "smokebench")]
pub const NOP: usize = 2_500_000;
#[cfg(not(feature = "smokebench"))]
pub const NOP: usize = 25_000_000;


use std::env;
fn main() {
    let _r = env_logger::try_init();
    if cfg!(feature = "smokebench") {
        warn!("Running with feature 'smokebench' may not get the desired results");
    }

    bench_utils::disable_dvfs();

    let args: Vec<String> = env::args().collect();
    if args.len() != 6 {
        println!("Usage: cargo run -- n_threads reads_pct, runtime, numa_policy, run_id_num");
    }

    let n_threads = args[1].parse::<usize>().unwrap();
    let reads_pct = args[2].parse::<usize>().unwrap();
    let write_ratio = 100 - reads_pct;
    let runtime = args[3].parse::<usize>().unwrap();
    let numa_policy = match args[4].as_str() {
        "fill" => ThreadMapping::NUMAFill,
        "interleave" => ThreadMapping::Interleave,
        _ => panic!("supply fill or interleave as numa mapping")
    };
    let run_id_num = args[5].parse::<usize>().unwrap();

    let mut harness = TestHarness::new(Duration::from_secs(10));


    let ops = generate_operations(NOP, write_ratio);
    let bench_name = format!("nr_vspace-{}-{}-{}-{}", n_threads, write_ratio, numa_policy, run_id_num);

    mkbench::ScaleBenchBuilder::<R>::new(ops)
        .threads(n_threads)
        .update_batch(32)
        .log_size(2 * 1024 * 1024)
        .replica_strategy(mkbench::ReplicaStrategy::Socket)
        .thread_mapping(numa_policy)
        .log_strategy(mkbench::LogStrategy::One)
        .configure(
            c,
            &bench_name,
            |_cid, tkn, replica, op, _batch_size| match op {
                Operation::ReadOperation(op) => {
                    replica.execute(*op, tkn);
                    tkn
                }
                Operation::WriteOperation(op) => {
                    replica.execute_mut(*op, tkn);
                    tkn
                }
            },
        );
}