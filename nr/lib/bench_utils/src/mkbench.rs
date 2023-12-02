// Copyright © 2019-2022 VMware, Inc. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Benchmark harness runner to instantiate and configure benchmarks.
//!
//! The file exports two items:
//!  - baseline_comparison: A generic function to compare a data-structure with
//!    and without a log.
//! - `ScaleBenchBuilder`: A struct that helps to configure criterion to
//!    evaluate the scalability of a data-structure with node-replication.

use std::collections::HashMap;
use std::fmt::{self};
use std::fs::OpenOptions;
use std::hint::black_box;
use std::marker::{PhantomData, Send, Sync};
use std::num::NonZeroUsize;
use std::path::Path;
use std::sync::{Arc, Barrier};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use csv::WriterBuilder;
use log::*;

const MY_DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;

#[cfg(feature = "unverified")]
use node_replication::{Dispatch, Log, Replica, ReplicaToken, MAX_REPLICAS_PER_LOG};

#[cfg(feature = "unverified")]
#[derive(Debug, Clone, Copy)]
pub struct ThreadToken {
    pub(crate) tid: ReplicaToken,
    pub(crate) rid: ReplicaId,
}

#[cfg(feature = "unverified")]
impl ThreadToken {
    pub fn thread_id(&self) -> usize {
        // self.tid
        99
    }
    pub fn replica_id(&self) -> usize {
        self.rid
    }
}

#[cfg(feature = "unverified")]
type ReplicaId = usize;

#[cfg(feature = "verified")]
use verus_nr::{Dispatch, AffinityFn, NodeReplicated, NR, ReplicaId, ThreadToken};


use rand::seq::SliceRandom;
use rand::SeedableRng;
// use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use serde::Serialize;

pub use crate::topology::ThreadMapping;
use crate::{benchmark::*, topology::*, Operation};

pub fn chg_affinity(rid: ReplicaId) {
    let mut cpu: usize = 0;
    let mut node: usize = 0;
    unsafe { nix::libc::syscall(nix::libc::SYS_getcpu, &mut cpu, &mut node, 0) };

    let mut cpu_set = nix::sched::CpuSet::new();
    trace!(
        "cpus for node={} are {:#?}",
        rid,
        MACHINE_TOPOLOGY.cpus_on_node(rid as u64)
    );
    for ncpu in MACHINE_TOPOLOGY.cpus_on_node(rid as u64) {
        debug!("ncpu is {:?}", ncpu);
        cpu_set
            .set(ncpu.cpu as usize)
            .expect("Can't toggle CPU in cpu_set");
    }
    debug!(
        "we are on cpu {} node {} and should handle things for replica {} now, changing affinity to {:?}",
        cpu, node, rid, cpu_set
    );
    nix::sched::sched_setaffinity(nix::unistd::Pid::from_raw(0), &cpu_set)
        .expect("Can't change thread affinity");
}

/// Threshold after how many iterations we log a warning for busy spinning loops.
///
/// This helps with debugging to figure out where things may end up blocking.
/// Should be a power of two to avoid divisions.
pub const WARN_THRESHOLD: usize = 1 << 28;

/// Record a thread records during benchmarking, stored to a file later.
#[derive(Serialize)]
struct Record {
    name: String,
    rs: ReplicaStrategy,
    tm: ThreadMapping,
    batch_size: usize,
    threads: usize,
    duration: f64,
    thread_id: usize,
    core_id: u64,
    exp_time_in_sec: usize,
    iterations: usize,
}

/// The function that executes the benchmark operation.
#[cfg(feature = "unverified")]
type BenchFn<R> = fn(
    tid: crate::ThreadId,
    idx: ThreadToken,
    replica: &Arc<R>,
    operations: &Operation<
        <<R as DsInterface>::D as Dispatch>::ReadOperation,
        <<R as DsInterface>::D as Dispatch>::WriteOperation,
    >,
    usize,
) -> ThreadToken;

#[cfg(feature = "verified")]
/// The function that executes the benchmark operation.
type BenchFn<R> = fn(
    tid: crate::ThreadId,
    idx: ThreadToken<<R as DsInterface>::D>,
    replica: &Arc<R>,
    operations: &Operation<
        <<R as DsInterface>::D as Dispatch>::ReadOperation,
        <<R as DsInterface>::D as Dispatch>::WriteOperation,
    >,
    usize,
) -> ThreadToken<<R as DsInterface>::D>;

/// The interface a data-structure must implement to be benchmarked by
/// `ScaleBench`.
#[cfg(feature = "unverified")]
pub trait DsInterface {
    type D: Dispatch + Default + Sync;

    /// Allocate a new data-structure.
    ///
    /// - `replicas`: How many replicas the data-structure should maintain.
    /// - `logs`: How many logs the data-structure should be partitioned over.
    fn new(replicas: NonZeroUsize, logs: NonZeroUsize, log_size: usize) -> Arc<Self>;

    /// Register a thread with a data-structure.
    ///
    /// - `rid` indicates which replica the thread should use.
    fn register(&self, rid: ReplicaId) -> Option<ThreadToken>;

    /// Apply a mutable operation to the data-structure.
    fn execute_mut(
        &self,
        op: <Self::D as Dispatch>::WriteOperation,
        idx: ThreadToken,
    ) -> <Self::D as Dispatch>::Response;

    /// Apply a immutable operation to the data-structure.
    fn execute(
        &self,
        op: <Self::D as Dispatch>::ReadOperation,
        idx: ThreadToken,
    ) -> <Self::D as Dispatch>::Response;
}

#[cfg(feature = "unverified")]
pub struct NodeReplicated<'a, D: Dispatch + Sync> {
    log: Arc<Log<'a, D::WriteOperation>>,
    replicas: Vec<Arc<Replica<'a, D>>>,
}

#[cfg(feature = "unverified")]
impl<D> NodeReplicated<'_, D>
where
    D: Default + Dispatch + Sized + Sync,
{
    pub fn with_log_size(
        num_replicas: NonZeroUsize,
        log_size: usize,
    ) -> Self {
        assert!(num_replicas.get() < MAX_REPLICAS_PER_LOG);

        chg_affinity(0);
        let log = Arc::new(Log::new(log_size));

        let mut replicas = Vec::new();
        replicas.try_reserve(num_replicas.get()).expect("failed to reserve storage for replicas");

        for replica_id in 0..num_replicas.get() {
            let r = {
                chg_affinity(replica_id);
                Replica::<D>::new(&log)
            };

            // This succeeds, we did `try_reserve` earlier so no `try_push` is
            // necessary.
            replicas.push(r);
        }

        chg_affinity(0);

        NodeReplicated {
            replicas,
            log,
        }
    }

    pub fn register(&self, replica_id: ReplicaId) -> Option<ThreadToken> {
        if replica_id < self.replicas.len() {
            let rtkn = self.replicas[replica_id].register()?;
            Some(ThreadToken {
                tid: rtkn,
                rid: replica_id,
            })
        } else {
            None
        }
    }

    fn execute_mut(
        &self,
        op: <D as Dispatch>::WriteOperation,
        idx: ThreadToken,
    ) -> <D as Dispatch>::Response {
        self.replicas[idx.rid].execute_mut(op, idx.tid)
    }

    fn execute(
        &self,
        op: <D as Dispatch>::ReadOperation,
        idx: ThreadToken,
    ) -> <D as Dispatch>::Response {
        self.replicas[idx.rid].execute(op, idx.tid)
    }

}

#[cfg(feature = "unverified")]
impl<'a, T: Dispatch + Sync + Default> DsInterface for NodeReplicated<'_, T> {
    type D = T;

    fn new(replicas: NonZeroUsize, _logs: NonZeroUsize, log_size: usize) -> Arc<Self> {
        Arc::new(
            NodeReplicated::with_log_size(replicas, log_size)
        )
    }

    fn register(&self, rid: ReplicaId) -> Option<ThreadToken> {
        NodeReplicated::register(self, rid)
    }

    fn execute_mut(
        &self,
        op: <Self::D as Dispatch>::WriteOperation,
        idx: ThreadToken,
    ) -> <Self::D as Dispatch>::Response {
        NodeReplicated::execute_mut(self, op, idx)
    }

    fn execute(
        &self,
        op: <Self::D as Dispatch>::ReadOperation,
        idx: ThreadToken,
    ) -> <Self::D as Dispatch>::Response {
        NodeReplicated::execute(self, op, idx)
    }
}


/// The interface a data-structure must implement to be benchmarked by
/// `ScaleBench`.
#[cfg(feature = "verified")]
pub trait DsInterface {
    type D: Dispatch + Default + Sync;

    /// Allocate a new data-structure.
    ///
    /// - `replicas`: How many replicas the data-structure should maintain.
    /// - `logs`: How many logs the data-structure should be partitioned over.
    fn new(replicas: NonZeroUsize, logs: NonZeroUsize, log_size: usize) -> Self;

    /// Register a thread with a data-structure.
    ///
    /// - `rid` indicates which replica the thread should use.
    fn register(&mut self, rid: ReplicaId) -> Option<ThreadToken<Self::D >>;

    /// Apply a mutable operation to the data-structure.
    fn execute_mut(
        &self,
        op: <Self::D as Dispatch>::WriteOperation,
        idx: ThreadToken<Self::D >,
    ) -> Result<(<Self::D as Dispatch>::Response, ThreadToken<Self::D >), ThreadToken<Self::D >>;

    /// Apply a immutable operation to the data-structure.
    fn execute(
        &self,
        op: <Self::D as Dispatch>::ReadOperation,
        idx: ThreadToken<Self::D >,
    ) -> Result<(<Self::D as Dispatch>::Response, ThreadToken<Self::D >), ThreadToken<Self::D >>;
}


/// How replicas are mapped to cores/threads.
#[derive(Serialize, Copy, Clone, Eq, PartialEq)]
pub enum ReplicaStrategy {
    /// One replica per system.
    One,
    /// One replica per L1 cache.
    L1,
    /// One replica per L2 cache.
    L2,
    /// One replica per L3 cache.
    L3,
    /// One replica per socket.
    Socket,
    /// One for every hardware thread.
    PerThread,
}

impl fmt::Display for ReplicaStrategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ReplicaStrategy::One => write!(f, "System"),
            ReplicaStrategy::L1 => write!(f, "L1"),
            ReplicaStrategy::L2 => write!(f, "L2"),
            ReplicaStrategy::L3 => write!(f, "L3"),
            ReplicaStrategy::Socket => write!(f, "Socket"),
            ReplicaStrategy::PerThread => write!(f, "PerThread"),
        }
    }
}

impl fmt::Debug for ReplicaStrategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ReplicaStrategy::One => write!(f, "RS=System"),
            ReplicaStrategy::L1 => write!(f, "RS=L1"),
            ReplicaStrategy::L2 => write!(f, "RS=L2"),
            ReplicaStrategy::L3 => write!(f, "RS=L3"),
            ReplicaStrategy::Socket => write!(f, "RS=Socket"),
            ReplicaStrategy::PerThread => write!(f, "RS=PerThread"),
        }
    }
}

/// How logs are mapped to cores/threads.
#[derive(Serialize, Copy, Clone, Eq, PartialEq)]
pub enum LogStrategy {
    /// One Log per system.
    One,
    /// One log for every hardware thread.
    PerThread,
    /// Custom number of logs.
    Custom(usize),
}

impl fmt::Display for LogStrategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LogStrategy::One => write!(f, "System"),
            LogStrategy::PerThread => write!(f, "PerThread"),
            LogStrategy::Custom(v) => write!(f, "Custom({})", v),
        }
    }
}

impl fmt::Debug for LogStrategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LogStrategy::One => write!(f, "LS=System"),
            LogStrategy::PerThread => write!(f, "LS=PerThread"),
            LogStrategy::Custom(v) => write!(f, "LS=Custom({})", v),
        }
    }
}

pub struct ScaleBenchmark<R: DsInterface>
where
    <R::D as Dispatch>::WriteOperation: Sync + Send + Copy + PartialEq + 'static,
    <R::D as Dispatch>::ReadOperation: Sync + Send + Copy,
    <R::D as Dispatch>::Response: Send,
    R::D: Sync + Dispatch + Default + Send,
{
    /// Name of the benchmark
    name: String,
    /// ReplicaStrategy used by the benchmark
    rs: ReplicaStrategy,
    /// ThreadMapping used by the benchmark
    tm: ThreadMapping,
    /// Total amount of threads used by the benchmark
    ts: usize,
    /// ReplicaStrategy used by the benchmark
    ls: LogStrategy,
    /// Replica <-> Thread/Cpu mapping as used by the benchmark.
    rm: HashMap<ReplicaId, Vec<Cpu>>,
    /// Size of the operation log
    log_size: usize,
    /// An Arc reference to operations executed on the log.
    operations: Arc<
        Vec<
            Operation<
                <R::D as Dispatch>::ReadOperation,
                <R::D as Dispatch>::WriteOperation,
            >,
        >,
    >,
    duration: Duration,
    /// Batch-size (passed as a parameter to benchmark funtion `f`)
    batch_size: usize,
    /// Benchmark function to execute
    f: BenchFn<R>,
    /// Thread handles
    handles: Vec<JoinHandle<(Core, Vec<usize>)>>,
    /// Where to write the results
    file_name: &'static str,
}

impl<R: 'static> ScaleBenchmark<R>
where
    <R::D as Dispatch>::WriteOperation: Send + Sync + Copy + PartialEq,
    <R::D as Dispatch>::ReadOperation: Send + Sync + Copy,
    <R::D as Dispatch>::Response: Send,
    R::D: 'static + Sync + Dispatch + Default + Send,
    R: DsInterface + Sync + Send,
{
    /// Create a new ScaleBenchmark.
    fn new(
        name: String,
        topology: &MachineTopology,
        rs: ReplicaStrategy,
        ls: LogStrategy,
        tm: ThreadMapping,
        ts: usize,
        log_size: usize,
        duration: Duration,
        operations: Vec<
            Operation<
                <R::D as Dispatch>::ReadOperation,
                <R::D as Dispatch>::WriteOperation,
            >,
        >,
        batch_size: usize,
        f: BenchFn<R>,
    ) -> ScaleBenchmark<R>
    where
        R: Sync,
    {
        // Log the per-thread runtimes to the CSV file
        let file_name = "scaleout_benchmarks.csv";

        ScaleBenchmark {
            name,
            rs,
            ls,
            tm,
            ts,
            log_size,
            rm: ScaleBenchmark::<R>::replica_core_allocation(topology, rs, tm, ts),
            duration,
            operations: Arc::new(operations),
            batch_size,
            f,
            handles: Default::default(),
            file_name,
        }
    }

    /// Return the amount of threads created by this benchmark.
    fn threads(&self) -> usize {
        // aggregate cores per replica, then sum them all
        self.rm.values().map(|v| v.len()).sum()
    }

    /// Return the amount of replias created by this benchmark.
    fn replicas(&self) -> usize {
        self.rm.len()
    }

    /// Terminate the worker threads by sending 0 to the iter channel:
    fn terminate(self) -> std::io::Result<()> {
        let mut all_results = Vec::<(Core, usize, Vec<usize>)>::with_capacity(self.handles.len());
        let mut everything =
            Vec::<usize>::with_capacity(self.handles.len() * self.duration.as_secs() as usize);

        for (tid, handle) in self.handles.into_iter().enumerate() {
            let (cid, thread_results) = handle.join().unwrap();
            everything.extend(&thread_results);
            all_results.push((cid, tid, thread_results));
        }

        if cfg!(not(feature = "smokebench")) {
            let avg = crate::benchmark::mean(&everything).unwrap();
            let stdev = crate::benchmark::std_deviation(&everything).unwrap();
            println!(
                "Run({:?} {:?} {:3} {:?} BS={}) => {:20.5} ({:.5})",
                self.rs,
                self.tm,
                self.ts,
                self.ls,
                self.batch_size,
                avg * (self.ts as f64),
                stdev
            );
        } else {
            println!(
                "Run({:?} {:?} {:?} {:?} BS={}) => not measured",
                self.rs, self.tm, self.ts, self.ls, self.batch_size,
            );
        }

        let write_headers = !Path::new(self.file_name).exists(); // write headers only to new file
        let csv_file = OpenOptions::new()
            .append(true)
            .create(true)
            .open(self.file_name)?;

        let mut wtr = WriterBuilder::new()
            .has_headers(write_headers)
            .from_writer(csv_file);

        for (cid, tid, ops_per_sec) in all_results.iter() {
            for (idx, ops) in ops_per_sec.iter().enumerate() {
                let record = Record {
                    name: self.name.clone(),
                    rs: self.rs,
                    tm: self.tm,
                    batch_size: self.batch_size,
                    threads: self.ts,
                    duration: Duration::from_secs(10).as_secs_f64(),
                    thread_id: *tid,
                    core_id: *cid,
                    exp_time_in_sec: idx + 1, // start at 1 (for first second)
                    iterations: *ops,
                };
                wtr.serialize(record)
                    .expect("Failed to serialize benchmark record");
            }
        }
        wtr.flush()?;

        Ok(())
    }

    fn startup(&mut self) {
        let thread_num = self.threads();

        let start_sync = Arc::new(Barrier::new(thread_num));
        let replicas = NonZeroUsize::new(self.replicas()).unwrap();
        let mut ds = R::new(replicas, NonZeroUsize::new(1).unwrap(), self.log_size);

        #[cfg(feature = "verified")]
        let mut thread_tokens = {
            let mut thread_tokens =  HashMap::with_capacity(replicas.into());
            for (rid, cores) in self.rm.clone().into_iter() {
                if thread_tokens.contains_key(&rid) {
                    let tks : &mut Vec<ThreadToken<R::D>> = thread_tokens.get_mut(&rid).unwrap();
                    tks.extend(cores.iter().map(|_| ds.register(rid).unwrap()));
                } else {
                    let mut tks :  Vec<ThreadToken<R::D>> = Vec::new();
                    thread_tokens.insert(rid, cores.iter().map(|_| ds.register(rid).unwrap()).collect());
                }
            }
            thread_tokens
        };

        #[cfg(feature = "verified")]
        let ds = Arc::new(ds);

        debug!(
            "Execute benchmark {} with the following replica: [core_id] mapping: {:#?}",
            self.name, self.rm
        );
        for (rid, cores) in self.rm.clone().into_iter() {
            for core_id in cores {
                // Pin thread to force the allocations below (`operations` etc.)
                // with the correct NUMA affinity
                crate::pin_thread(core_id);

                let start_sync = start_sync.clone();

                let ds = ds.clone();
                let f = self.f.clone();
                let batch_size = self.batch_size;
                let log_period = Duration::from_secs(1);
                let name = self.name.clone();
                let operations = self.operations.clone();
                let duration = self.duration.clone();

                #[cfg(feature = "verified")]
                let mut thread_token = thread_tokens.get_mut(&rid).unwrap().pop().expect("Can't register replica, out of slots?");

                self.handles.push(thread::spawn(move || {
                    crate::pin_thread(core_id);

                    #[cfg(feature = "unverified")]
                    let mut thread_token = ds
                        .register(rid)
                        .expect("Can't register replica, out of slots?");

                    // Copy the actual Vec<Operations> data within the thread
                    let mut operations = (*operations).clone();
                    operations.shuffle(&mut ChaCha8Rng::seed_from_u64(42 + core_id));

                    debug!(
                        "Running {:?} on core {} replica#{} rtoken#{:?}.{:?} for {:?}",
                        thread::current().id(),
                        core_id,
                        rid,
                        thread_token.replica_id(),
                        thread_token.thread_id(),
                        duration
                    );

                    let mut operations_per_second: Vec<usize> = Vec::with_capacity(128);
                    let mut operations_completed: usize = 0;
                    let mut iter: usize = 0;
                    let nop: usize = operations.len();

                    start_sync.wait();
                    let start = Instant::now();
                    let end_experiment = start + duration;
                    let mut next_log = start + log_period;

                    while Instant::now() < end_experiment {
                        for _i in 0..batch_size {
                            thread_token = black_box((f)(
                                core_id,
                                thread_token,
                                &ds,
                                &operations[iter],
                                batch_size,
                            ));

                            iter = (iter + 1) % nop;
                        }
                        operations_completed += 1 * batch_size;

                        if Instant::now() >= next_log {
                            trace!("Operations completed {} / s", operations_completed);
                            operations_per_second.push(operations_completed);
                            // reset operations completed
                            operations_completed = 0;
                            next_log += log_period;
                        }
                    }

                    debug!(
                        "Completed {:?} on core {} replica#{} rtoken#{:?}.{:?} did {} ops in {:?}",
                        thread::current().id(),
                        core_id,
                        rid,
                        thread_token.replica_id(),
                        thread_token.thread_id(),
                        operations_completed,
                        duration
                    );

                    if name.starts_with("urcu") {
                        unsafe {
                            urcu_sys::rcu_unregister_thread();
                        }
                    }

                    start_sync.wait();
                    (core_id, operations_per_second)
                }));
            }
        }
    }

    /// Calculates how to divide threads among replicas and CPU.
    ///
    /// This is a function based on how many threads we have, how we map
    /// them onto the CPUs, the granularity of replicas, and the topology of the
    /// underlying hardware.
    fn replica_core_allocation(
        topology: &MachineTopology,
        rs: ReplicaStrategy,
        tm: ThreadMapping,
        ts: usize,
    ) -> HashMap<usize, Vec<Cpu>> {
        let cpus = topology.allocate(tm, ts, true);
        debug_assert_eq!(ts, cpus.len());

        trace!(
            "Allocated cores for benchmark with {:?} {:?} {:?}",
            rs,
            tm,
            cpus
        );
        let mut rm: HashMap<usize, Vec<Cpu>> = HashMap::new();

        match rs {
            ReplicaStrategy::One => {
                rm.insert(0, cpus.iter().map(|c| c.cpu).collect());
            }
            ReplicaStrategy::Socket => {
                let mut sockets: Vec<Socket> = cpus.iter().map(|t| t.socket).collect();
                sockets.sort();
                sockets.dedup();

                for s in sockets {
                    rm.insert(
                        s as usize,
                        cpus.iter()
                            .filter(|c| c.socket == s)
                            .map(|c| c.cpu)
                            .collect(),
                    );
                }
            }
            ReplicaStrategy::L1 => match tm {
                ThreadMapping::None => {}
                ThreadMapping::Sequential => {
                    let mut l1: Vec<L1> = cpus.iter().map(|t| t.l1).collect();
                    l1.sort();
                    l1.dedup();

                    for s in l1 {
                        rm.insert(
                            s as usize,
                            cpus.iter().filter(|c| c.l1 == s).map(|c| c.cpu).collect(),
                        );
                    }
                }
                ThreadMapping::NUMAFill => {
                    unimplemented!();
                }
                // Giving replica number based on L1 number won't work in this case, as the
                // L1 numbers are allocated to Node-0 first and then to Node-1, and so on.
                ThreadMapping::Interleave => {
                    let mut l1: Vec<L1> = cpus.iter().map(|t| t.l1).collect();
                    l1.sort();
                    l1.dedup();

                    let mut rid = 0;
                    let mut mapping: HashMap<L1, usize> = HashMap::with_capacity(cpus.len());
                    for cpu in cpus.iter() {
                        let cache_num = cpu.l1;
                        if mapping.get(&cache_num).is_none() {
                            mapping.insert(cache_num, rid);
                            rid += 1;
                        }
                    }

                    for s in l1 {
                        rm.insert(
                            *mapping.get(&s).unwrap(),
                            cpus.iter().filter(|c| c.l1 == s).map(|c| c.cpu).collect(),
                        );
                    }
                }
            },
            ReplicaStrategy::L2 => {
                let mut l2: Vec<L2> = cpus.iter().map(|t| t.l2).collect();
                l2.sort();
                l2.dedup();

                for s in l2 {
                    rm.insert(
                        s as usize,
                        cpus.iter().filter(|c| c.l2 == s).map(|c| c.cpu).collect(),
                    );
                }
            }
            ReplicaStrategy::L3 => {
                let mut l3: Vec<L3> = cpus.iter().map(|t| t.l3).collect();
                l3.sort();
                l3.dedup();

                for s in l3 {
                    rm.insert(
                        s as usize,
                        cpus.iter().filter(|c| c.l3 == s).map(|c| c.cpu).collect(),
                    );
                }
            }
            ReplicaStrategy::PerThread => {
                for (idx, core) in cpus.iter().map(|c| c.cpu).enumerate() {
                    rm.insert(idx, vec![core]);
                }
            }
        };

        rm
    }
}

/// A generic benchmark configurator for node-replication scalability benchmarks.
pub struct ScaleBenchBuilder<R: DsInterface>
where
    <R::D as Dispatch>::WriteOperation: Sync + Send + PartialEq + Clone + 'static,
    <R::D as Dispatch>::ReadOperation: Sync + Send,
    <R::D as Dispatch>::Response: Send,
    R::D: 'static + Sync + Dispatch + Default,
{
    /// Replica granularity.
    replica_strategies: Vec<ReplicaStrategy>,
    /// Log granularity.
    log_strategies: Vec<LogStrategy>,
    /// Thread assignments.
    thread_mappings: Vec<ThreadMapping>,
    /// # Threads.
    threads: Vec<usize>,
    /// Batch sizes to use (default 1)
    batches: Vec<usize>,
    /// Size of the operation log(s) that get created for the benchmark
    log_size: usize,
    /// Operations executed on the log.
    operations: Vec<
        Operation<<R::D as Dispatch>::ReadOperation, <R::D as Dispatch>::WriteOperation>,
    >,
    /// Marker for R
    _marker: PhantomData<R>,
}

impl<R: 'static + DsInterface> ScaleBenchBuilder<R>
where
    R::D: Dispatch + Default + Send + Sync,
    <R::D as Dispatch>::WriteOperation: Send + Sync + PartialEq + Clone,
    <R::D as Dispatch>::ReadOperation: Sync + Send,
    <R::D as Dispatch>::Response: Send,
{
    /// Initialize an "empty" ScaleBenchBuilder with a  MiB log.
    ///
    /// By default this won't execute any runs,
    /// you have to at least call `threads`, `thread_mapping`
    /// `replica_strategy` once and set `operations`.
    pub fn new(
        ops: Vec<
            Operation<
                <R::D as Dispatch>::ReadOperation,
                <R::D as Dispatch>::WriteOperation,
            >,
        >,
    ) -> ScaleBenchBuilder<R> {
        ScaleBenchBuilder {
            replica_strategies: Vec::new(),
            log_strategies: Vec::new(),
            thread_mappings: Vec::new(),
            threads: Vec::new(),
            log_size: MY_DEFAULT_LOG_BYTES,
            batches: vec![1usize],
            operations: ops,
            _marker: PhantomData,
        }
    }

    /// Configures the builder automatically based on the underlying machine properties.
    pub fn machine_defaults(&mut self) -> &mut Self {
        self.thread_mapping(ThreadMapping::Sequential);
        #[cfg(feature = "exhaustive")]
        self.replica_strategy(ReplicaStrategy::One);
        self.replica_strategy(ReplicaStrategy::Socket);
        #[cfg(feature = "exhaustive")]
        self.replica_strategy(ReplicaStrategy::L1);
        self.thread_defaults()
    }

    pub fn thread_defaults(&mut self) -> &mut Self {
        let topology = MachineTopology::new();
        let max_cores = topology.cores();

        let sockets = topology.sockets();
        let cores_on_s0 = topology.cpus_on_socket(sockets[0]);
        let step_size = cores_on_s0.len() / 4;
        for t in (0..(max_cores + 1)).step_by(step_size) {
            if t == 0 {
                // Can't run on 0 threads
                self.threads(t + 1);
            } else {
                self.threads(t);
            }
        }

        self.threads.sort();
        self
    }

    /// Run benchmark with batching of size `b`.
    pub fn add_batch(&mut self, b: usize) -> &mut Self {
        self.batches.push(b);
        self
    }

    pub fn update_batch(&mut self, b: usize) -> &mut Self {
        self.batches.clear();
        self.batches.push(b);
        self
    }

    /// Run benchmark with `t` threads.
    pub fn threads(&mut self, t: usize) -> &mut Self {
        self.threads.push(t);
        self
    }

    /// Run benchmark with given thread <-> machine mapping.
    pub fn thread_mapping(&mut self, tm: ThreadMapping) -> &mut Self {
        self.thread_mappings.push(tm);
        self
    }

    /// Run benchmark with given replication strategy.
    pub fn replica_strategy(&mut self, rs: ReplicaStrategy) -> &mut Self {
        self.replica_strategies.push(rs);
        self
    }

    /// Run benchmark with given replication strategy.
    pub fn log_strategy(&mut self, ls: LogStrategy) -> &mut Self {
        self.log_strategies.push(ls);
        self
    }

    /// Set the size of the operation log
    pub fn log_size(&mut self, ls: usize) -> &mut Self {
        self.log_size = ls;
        self
    }

    /// Creates a benchmark to evalute the scalability properties of the
    /// log for a given data-structure.
    ///
    /// This configures the supplied criterion runner to execute
    /// as many benchmarks as result from the configuration options set in the
    /// ScaleBenchBuilder arguments.
    ///
    /// TestHarness will be configured to create a run for every
    /// possible triplet: (replica strategy, thread mapping, #threads).
    pub fn configure(&self, c: &mut TestHarness, name: &str, f: BenchFn<R>)
    where
        <R::D as Dispatch>::WriteOperation: Sync + Send + Copy + PartialEq + 'static,
        <R::D as Dispatch>::ReadOperation: Sync + Send + Copy + Clone,
        <R::D as Dispatch>::Response: Send,
        R: DsInterface + Sync + Send,
        R::D: 'static + Send + Sync,
    {
        let topology = MachineTopology::new();
        crate::disable_dvfs();
        println!("{}", name);

        for rs in self.replica_strategies.iter() {
            for ls in self.log_strategies.iter() {
                for tm in self.thread_mappings.iter() {
                    for ts in self.threads.iter() {
                        for b in self.batches.iter() {
                            let mut runner = ScaleBenchmark::<R>::new(
                                String::from(name),
                                &topology,
                                *rs,
                                *ls,
                                *tm,
                                *ts,
                                self.log_size,
                                c.duration,
                                self.operations.to_vec(),
                                *b,
                                f,
                            );
                            runner.startup();
                            runner
                                .terminate()
                                .expect("Couldn't terminate the experiment");
                        }
                    }
                }
            }
        }
    }
}
