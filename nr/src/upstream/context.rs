// Copyright © 2019-2022 VMware, Inc. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Context where threads "buffer" operations until they are completed.
//!
//! This allows the combiner to find and flat-combine operations.

use core::cell::{Cell, UnsafeCell};
use core::default::Default;
use core::iter::{ExactSizeIterator, Iterator};
use core::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;
use static_assertions::const_assert;

/// The maximum number of operations that can be batched inside this context.
#[cfg(not(loom))]
pub const MAX_PENDING_OPS: usize = 32;
#[cfg(loom)]
pub(crate) const MAX_PENDING_OPS: usize = 1;
// This constant must be a power of two for `index()` to work.
const_assert!(MAX_PENDING_OPS.is_power_of_two());

/// Data for a pending operation.
///
/// It is a combination of the actual operation (`T`), the corresponding
/// expected result (`R`), along with potential meta-data (`M`) to keep track of
/// other things.
pub struct PendingOperation<T, R, M> {
    pub(crate) op: UnsafeCell<Option<T>>,
    pub(crate) resp: Cell<Option<R>>,
    pub(crate) meta: UnsafeCell<M>,
}

impl<T, R, M> Default for PendingOperation<T, R, M>
where
    M: Default,
{
    fn default() -> Self {
        PendingOperation {
            op: UnsafeCell::new(None),
            resp: Cell::new(None),
            meta: Default::default(),
        }
    }
}

/// Contains state of a particular thread w.r.g. to outstanding operations.
///
/// The primary purpose of this type is to batch operations issued on a thread
/// before appending them to the shared log. This is achieved using a fix sized
/// buffer. Once operations are executed against the replica, the results of the
/// operations are stored back into the same buffer.
///
/// # Generic arguments
///
/// - `T` should identify operations issued by the thread (an opcode of sorts)
/// and should also contain arguments/parameters required to execute these
/// operations on the replicas.
///
/// - `R` is the type of the result obtained when an operation is executed
/// against the replica.
///
/// - `M` is the type of meta-data that is associated with each operation.
#[repr(align(64))]
pub(crate) struct Context<T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
{
    /// Array that will hold all pending operations to be appended to the shared
    /// log as well as the results obtained on executing them against a replica.
    pub(crate) batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS],

    /// Logical array index at which new operations will be enqueued into the
    /// batch. This variable is updated by the thread that owns this context,
    /// and is read by the combiner.
    pub tail: CachePadded<AtomicUsize>,

    /// Logical array index from which any attempt to dequeue responses will be
    /// made. This variable is only accessed by the thread that owns this
    /// context.
    pub head: CachePadded<AtomicUsize>,

    /// Logical array index from which the operations will be dequeued for flat
    /// combining. This variable is updated by the combiner, and is read by the
    /// thread that owns this context.
    pub comb: CachePadded<AtomicUsize>,

    /// Identifies the context number within a replica. It also maps to the
    /// thread-id because the partitioned nature of the contexts in the replica.
    pub _idx: usize,
}

impl<T, R, M> Default for Context<T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
    M: Default,
{
    /// Default constructor for the context.
    fn default() -> Self {
        let mut batch: [CachePadded<PendingOperation<T, R, M>>; MAX_PENDING_OPS] =
            unsafe { ::core::mem::MaybeUninit::zeroed().assume_init() };
        for elem in &mut batch[..] {
            *elem = CachePadded::new(Default::default());
        }

        Context {
            batch,
            tail: CachePadded::new(AtomicUsize::new(0)),
            head: CachePadded::new(AtomicUsize::new(0)),
            comb: CachePadded::new(AtomicUsize::new(0)),
            _idx: 0,
        }
    }
}

impl<T, R, M> Context<T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
    M: Default,
{
    pub fn new(_idx: usize) -> Self {
        Self {
            _idx,
            ..Default::default()
        }
    }
}

impl<T, R, M> Context<T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
{
    /// Enqueues an operation onto this context's batch of pending operations.
    ///
    /// Returns true if the operation was successfully enqueued. False
    /// otherwise.
    #[inline(always)]
    pub(crate) fn enqueue(&self, op: T, meta: M) -> bool {
        let t = self.tail.load(Ordering::Acquire);
        let h = self.head.load(Ordering::Relaxed);

        // Check if we have space in the batch to hold this operation. If we
        // don't, then return false to the caller thread.
        if t - h == MAX_PENDING_OPS {
            return false;
        }

        // Add in the operation to the batch. Once added, update the tail so
        // that the combiner sees this operation. Relying on TSO here to make
        // sure that the tail is updated only after the operation has been
        // written in.
        let e = self.batch[self.index(t)].op.get();
        unsafe { *e = Some(op) };
        let me = self.batch[self.index(t)].meta.get();
        unsafe { *me = meta };

        self.tail.store(t + 1, Ordering::Release);
        true
    }

    /// Enqueues a batch of responses onto this context. This is invoked by the combiner
    /// after it has executed operations (obtained through a call to ops()) against the
    /// replica this thread is registered against.
    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn enqueue_resps(&self, responses: &[R]) {
        let n = responses.len();

        // Empty slice passed in; no work to do, so simply return.
        if n == 0 {
            return;
        };

        // Starting from `comb`, write all responses into the batch. Assume here that
        // the slice above doesn't cause us to cross the tail of the batch.
        for response in responses.iter().take(n) {
            self.enqueue_resp(response.clone());
        }
    }

    /// Enqueues a response onto this context. This is invoked by the combiner
    /// after it has executed operations (obtained through a call to ops()) against the
    /// replica this thread is registered against.
    #[inline(always)]
    pub(crate) fn enqueue_resp(&self, response: R) {
        let h = self.comb.load(Ordering::Relaxed);
        self.batch[self.index(h)].resp.replace(Some(response));
        self.comb.store(h + 1, Ordering::Relaxed);
    }

    /// Returns a single response if available. Otherwise, returns None.
    #[inline(always)]
    pub(crate) fn res(&self) -> Option<R> {
        let s = self.head.load(Ordering::Relaxed);
        let f = self.comb.load(Ordering::Relaxed);

        // No responses ready yet; return to the caller.
        if s == f {
            return None;
        };

        if s > f {
            panic!("Head of thread-local batch has advanced beyond combiner of.store!");
        }

        self.head.store(s + 1, Ordering::Relaxed);
        self.batch[self.index(s)].resp.take()
    }

    /// Adds any pending operations on this context to a passed in buffer.
    /// Returns the the number of such operations that were added in.
    #[inline(always)]
    pub(crate) fn iter(&self) -> ContextIterator<T, R, M>
    where
        M: Copy,
    {
        let h = self.comb.load(Ordering::Relaxed);
        let t = self.tail.load(Ordering::Relaxed);
        if h > t {
            panic!("Combiner Head of thread-local batch has advanced beyond tail!");
        }

        ContextIterator {
            cur: h,
            ctxt: self,
            h,
            t,
        }
    }

    /// Returns the maximum number of operations that will go pending on this context.
    #[inline(always)]
    pub(crate) fn batch_size() -> usize {
        MAX_PENDING_OPS
    }

    /// Given a logical address, returns an index into the batch at which it falls.
    #[inline(always)]
    pub(crate) fn index(&self, logical: usize) -> usize {
        logical & (MAX_PENDING_OPS - 1)
    }
}

/// Iterator for the currently active window of the per-thread context buffer.
///
/// # Note on safety
///
/// It's not a good idea to have a [`ContextIterator`] while the context head
/// and tail changes. Worst case will just panic due to unwrap on a None or give
/// incorrect results, but needs some thought: If worse things are possible, we
/// should instead make [`Context::iter`] unsafe.
pub(crate) struct ContextIterator<'s, T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
    M: Copy,
{
    // A reference to the per-thread context with the window we're iterating
    // over.
    ctxt: &'s Context<T, R, M>,
    /// Current index into the iteration window (h..t).
    cur: usize,
    /// The head (start) of the currently available context buffer window.
    h: usize,
    /// The tail (end) of the currently available context buffer window.
    t: usize,
}

/// We know the exact window size for the [`ContextIterator`], it's the range
/// from head to tail.
impl<'s, T, R, M> ExactSizeIterator for ContextIterator<'s, T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
    M: Copy,
{
    fn len(&self) -> usize {
        self.t - self.h
    }
}

/// We can iterator over the active window by calling `.next()` until it returns
/// None.
impl<'s, T, R, M> Iterator for ContextIterator<'s, T, R, M>
where
    T: Sized + Clone,
    R: Sized + Clone,
    M: Copy,
{
    type Item = (T, M);

    fn next(&mut self) -> Option<Self::Item> {
        // No operations on this thread; return to the caller indicating so.
        if self.len() == 0 {
            return None;
        }
        // Reached the end of the window.
        if self.cur == self.t {
            return None;
        }

        let e = &self.ctxt.batch[self.ctxt.index(self.cur)];
        let op = e.op.get();
        let meta = e.meta.get();
        self.cur += 1;

        unsafe { Some(((*op).clone().unwrap(), *meta)) }
    }
}
