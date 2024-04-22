#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;


verus! {

/// the maximum number of replicas
pub open const MAX_REPLICAS_PER_LOG: usize = 16;

/// the number of replicas we have
// pub open const NUM_REPLICAS: usize = 4;

#[verus::trusted]
pub open const MAX_REPLICAS: usize = 16;

/// the size of the log in bytes
pub open const DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;

// making the assumption here that the write operation is about 12-16 bytes..
pub open const LOG_SIZE: usize = 512 * 1024; // 4 * 1024 * 1024;

/// maximum number of threads per replica
pub open const MAX_THREADS_PER_REPLICA: usize = 64;

pub open const MAX_PENDING_OPS: usize = 1;

/// the maximum number of requests
pub open const MAX_REQUESTS: usize = MAX_THREADS_PER_REPLICA * MAX_PENDING_OPS;

/// interval when we do a try_combine when checking for responses
pub open const RESPONSE_CHECK_INTERVAL : usize = 0x2000_0000;

/// Constant required for garbage collection. When the tail and the head are these many
/// entries apart on the circular buffer, garbage collection will be performed by one of
/// the replicas registered with the log.
///
/// For the GC algorithm to work, we need to ensure that we can support the largest
/// possible append after deciding to perform GC. This largest possible append is when
/// every thread within a replica has a full batch of writes to be appended to the shared
/// log.
pub open const GC_FROM_HEAD: usize = MAX_PENDING_OPS * MAX_THREADS_PER_REPLICA;


/// Threshold after how many iterations we abort and report the replica we're waiting for
/// as stuck for busy spinning loops.
///
/// Should be a power of two to avoid divisions.
pub open const WARN_THRESHOLD: usize = 0x10000000;


pub open const MAX_IDX : u64 = 0xffff_ffff_f000_0000;

} // verus!
