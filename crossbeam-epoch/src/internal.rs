//! The global data and participant for garbage collection.
//!
//! # Registration
//!
//! In order to track all participants in one place, we need some form of participant
//! registration. When a participant is created, it is registered to a global lock-free
//! singly-linked list of registries; and when a participant is leaving, it is unregistered from the
//! list.
//!
//! # Pinning
//!
//! Every participant contains an integer that tells whether the participant is pinned and if so,
//! what was the global epoch at the time it was pinned. Participants also hold a pin counter that
//! aids in periodic global epoch advancement.
//!
//! When a participant is pinned, a `Guard` is returned as a witness that the participant is pinned.
//! Guards are necessary for performing atomic operations, and for freeing/dropping locations.
//!
//! # Thread-local bag
//!
//! Objects that get unlinked from concurrent data structures must be stashed away until the global
//! epoch sufficiently advances so that they become safe for destruction. Pointers to such objects
//! are pushed into a thread-local bag, and when it becomes full, the bag is marked with the current
//! global epoch and pushed into the global queue of bags. We store objects in thread-local storages
//! for amortizing the synchronization cost of pushing the garbages to a global queue.
//!
//! # Global queue
//!
//! Whenever a bag is pushed into a queue, the objects in some bags in the queue are collected and
//! destroyed along the way. This design reduces contention on data structures. The global queue
//! cannot be explicitly accessed: the only way to interact with it is by calling functions
//! `defer()` that adds an object tothe thread-local bag, or `collect()` that manually triggers
//! garbage collection.
//!
//! Ideally each instance of concurrent data structure may have its own queue that gets fully
//! destroyed as soon as the data structure gets dropped.

use core::cell::{Cell, UnsafeCell};
use core::mem::{self, ManuallyDrop};
use core::num::Wrapping;
use core::ptr;
use core::sync::atomic::{self, Ordering};
use core::ops::Deref;

use crossbeam_utils::CachePadded;

use atomic::{Atomic, Owned, Shared};
use bloom_filter::BloomFilter;
use collector::{Collector, LocalHandle};
use garbage::{Bag, Garbage};
use guard::{unprotected, Guard};
use hazard::HazardSet;
use sync::list::{repeat_iter, Entry, IsElement, IterError, List};
use sync::stack::Stack;

/// TODO
const EPOCH_WIDTH: u32 = 3;

bitflags! {
    struct StatusFlags: usize {
        const PINNED = 1 << EPOCH_WIDTH;
        const EPOCH  = (1 << EPOCH_WIDTH) - 1;
    }
}

impl StatusFlags {
    fn new(is_pinned: bool, epoch: usize) -> Self {
        let is_pinned = if is_pinned {
            Self::PINNED
        } else {
            Self::empty()
        };
        let epoch = Self::from_bits_truncate(epoch) & Self::EPOCH;
        is_pinned | epoch
    }

    fn is_pinned(self) -> bool {
        !(self & Self::PINNED).is_empty()
    }

    fn epoch(self) -> usize {
        (self & Self::EPOCH).bits()
    }
}

/// The global data for a garbage collector.
pub struct Global {
    /// The intrusive linked list of `Local`s.
    locals: List<Local>,

    /// The global pool of bags of deferred functions.
    bags: [CachePadded<Stack<Bag>>; 1 << EPOCH_WIDTH],

    /// The global status consisting of (1) the (approximate) summary of hazard pointers, and (2)
    /// the epoch.
    pub(crate) status: Atomic<CachePadded<BloomFilter>>,
}

impl Drop for Global {
    fn drop(&mut self) {
        unsafe {
            let status = self.status.load(Ordering::Relaxed, unprotected());
            drop(status.into_owned());
        }
    }
}

impl Global {
    /// Number of bags to destroy.
    const COLLECT_STEPS: usize = 8;

    /// Creates a new global data for garbage collection.
    #[inline]
    pub fn new() -> Self {
        Self {
            locals: List::new(),
            bags: [
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
                CachePadded::new(Stack::new()),
            ],
            status: Atomic::null(),
        }
    }

    /// Pushes the bag into the global queue and replaces the bag with a new empty bag.
    pub fn push_bag(&self, bag: &mut Bag, epoch: usize) {
        let bags = unsafe { &*self.bags.get_unchecked(epoch % (1 << EPOCH_WIDTH)) };
        let bag = mem::replace(bag, Bag::new());
        bags.push(bag);
    }

    #[inline]
    pub fn collect_inner<'g>(
        &'g self,
        status: Shared<'g, CachePadded<BloomFilter>>,
        guard: &'g Guard,
    ) -> bool {
        let flags = StatusFlags::from_bits_truncate(status.tag());
        let index = flags.epoch().wrapping_sub(3);
        let summary = unsafe { status.as_ref() }.map(Deref::deref);
        let steps = if cfg!(feature = "sanitize") {
            usize::max_value()
        } else {
            Self::COLLECT_STEPS
        };
        let bags = unsafe { &*self.bags.get_unchecked(index % (1 << EPOCH_WIDTH)) };

        for _ in 0..steps {
            if let Some(mut bag) = bags.try_pop(guard) {
                // Disposes the garbages (except for hazard pointers) in the bag popped from the
                // global queue.
                bag.dispose(summary);

                // If the bag is not empty (due to hazard pointers), push it back to the global
                // queue.
                if !bag.is_empty() {
                    self.push_bag(&mut bag, index.wrapping_add(1));
                }
            } else {
                return true;
            }
        }

        false
    }

    /// Collects several bags from the global queue and executes deferred functions in them.
    ///
    /// Note: This may itself produce garbage and in turn allocate new bags.
    ///
    /// `pin()` rarely calls `collect()`, so we want the compiler to place that call on a cold
    /// path. In other words, we want the compiler to optimize branching for the case when
    /// `collect()` is not called.
    #[cold]
    pub fn collect(&self, guard: &Guard) {
        let global_status = self.status.load(Ordering::Acquire, guard);
        if self.collect_inner(global_status, guard) {
            self.try_advance(guard);
        }
    }

    /// Attempts to advance the global epoch.
    ///
    /// The global epoch can advance only if all currently pinned participants have been pinned in
    /// the current epoch.
    ///
    /// Returns whether the global epoch has advanced.
    ///
    /// `try_advance()` is annotated `#[cold]` because it is rarely called.
    #[cold]
    pub fn try_advance(&self, guard: &Guard) -> bool {
        let global_status = self.status.load(Ordering::Relaxed, guard);
        let global_flags = StatusFlags::from_bits_truncate(global_status.tag());

        atomic::fence(Ordering::SeqCst);

        let mut summary = BloomFilter::new();

        // TODO(stjepang): `Local`s are stored in a linked list because linked lists are fairly
        // easy to implement in a lock-free manner. However, traversal can be slow due to cache
        // misses and data dependencies. We should experiment with other data structures as well.
        for local in self.locals.iter(guard) {
            match local {
                Err(IterError::Stalled) => {
                    // A concurrent thread stalled this iteration. That thread might also try to
                    // advance the epoch, in which case we leave the job to it. Otherwise, the
                    // epoch will not be advanced.
                    return false;
                }
                Ok(local) => {
                    let local_status = local.status.load(Ordering::Acquire, guard);
                    let local_flags = StatusFlags::from_bits_truncate(local_status.tag());

                    // If the participant was pinned in a different epoch, we cannot advance the
                    // global epoch just yet.
                    if local_flags.is_pinned() && local_flags.epoch() != global_flags.epoch() {
                        return false;
                    }

                    if let Some(local_summary) = unsafe { local_status.as_ref() } {
                        summary.union(local_summary);
                    }
                }
            }
        }

        // All pinned participants were pinned in the current global epoch. Now let's advance the
        // global epoch...
        //
        // But if the global epoch already has advanced, bail out.
        let global_status_validation = self.status.load(Ordering::Relaxed, guard);
        if global_status != global_status_validation {
            return false;
        }

        // Collects the old garbage bags.
        if !self.collect_inner(global_status, guard) {
            // There are remaining old garbage bags. We cannot advance the global epoch just yet.
            return false;
        }

        // Calculates the new global status.
        let new_flags = StatusFlags::new(false, global_flags.epoch().wrapping_add(1));
        let new_status = Owned::new(CachePadded::new(summary))
            .into_shared(guard)
            .with_tag(new_flags.bits());

        // Tries to replace the global status.
        self.status
            .compare_and_set(global_status, new_status, Ordering::Release, guard)
            // If successful, destroys the old summary.
            .map(|_| unsafe {
                if !global_status.is_null() {
                    guard.defer_destroy(global_status);
                }
            })
            // If unsuccessful, destroys the new summary.
            .map_err(|_| unsafe { drop(new_status.into_owned()) })
            // Returns whether the global epoch has advanced.
            .is_ok()
    }
}

/// Participant for garbage collection.
pub struct Local {
    /// A node in the intrusive linked list of `Local`s.
    entry: Entry,

    /// The local status consisting of (1) the (approximate) summary of hazard pointers, and (2)
    /// `StatusFlags`.
    status: Atomic<CachePadded<BloomFilter>>,

    /// A reference to the global data.
    ///
    /// When all guards and handles get dropped, this reference is destroyed.
    collector: UnsafeCell<ManuallyDrop<Collector>>,

    /// The local bag of deferred functions.
    pub(crate) bag: UnsafeCell<Bag>,

    /// The number of guards keeping this participant pinned.
    guard_count: Cell<usize>,

    /// The number of active handles.
    handle_count: Cell<usize>,

    /// Total number of pinnings performed.
    ///
    /// This is just an auxilliary counter that sometimes kicks off collection.
    pin_count: Cell<Wrapping<usize>>,

    /// The set of hazard pointers.
    pub(crate) hazards: HazardSet,
}

impl Local {
    /// Number of pinnings after which a participant will execute some deferred functions from the
    /// global queue.
    const PINNINGS_BETWEEN_COLLECT: usize = 32;

    /// Number of pinnings after which a participant will try to advance the global epoch.
    const PINNINGS_BETWEEN_TRY_ADVANCE: usize = 1024;

    /// Registers a new `Local` in the provided `Global`.
    pub fn register(collector: &Collector) -> LocalHandle {
        unsafe {
            // Since we dereference no pointers in this block, it is safe to use `unprotected`.

            let local = Owned::new(Local {
                entry: Entry::default(),
                status: Atomic::null(),
                collector: UnsafeCell::new(ManuallyDrop::new(collector.clone())),
                hazards: HazardSet::new(),
                bag: UnsafeCell::new(Bag::new()),
                guard_count: Cell::new(0),
                handle_count: Cell::new(1),
                pin_count: Cell::new(Wrapping(0)),
            })
            .into_shared(unprotected());
            collector.global.locals.insert(local);
            LocalHandle {
                local: local.as_raw(),
            }
        }
    }

    /// Returns a reference to the `Global` in which this `Local` resides.
    #[inline]
    pub fn global(&self) -> &Global {
        &self.collector().global
    }

    /// Returns a reference to the `Collector` in which this `Local` resides.
    #[inline]
    pub fn collector(&self) -> &Collector {
        unsafe { &**self.collector.get() }
    }

    /// Returns `true` if the current participant is pinned.
    #[inline]
    pub fn is_pinned(&self) -> bool {
        self.guard_count.get() > 0
    }

    /// Adds `deferred` to the thread-local bag.
    ///
    /// # Safety
    ///
    /// It should be safe for another thread to execute the given function.
    pub unsafe fn defer(&self, mut garbage: Garbage, guard: &Guard) {
        let bag = &mut *self.bag.get();

        while let Err(g) = bag.try_push(garbage) {
            let local_status = self.status.load(Ordering::Relaxed, guard);
            let local_flags = StatusFlags::from_bits_truncate(local_status.tag());
            self.global().push_bag(bag, local_flags.epoch());
            garbage = g;
        }
    }

    pub fn flush(&self, guard: &Guard) {
        let bag = unsafe { &mut *self.bag.get() };

        if !bag.is_empty() {
            let local_status = self.status.load(Ordering::Relaxed, guard);
            let local_flags = StatusFlags::from_bits_truncate(local_status.tag());
            self.global().push_bag(bag, local_flags.epoch());
        }

        self.global().collect(guard);
    }

    /// Pins the `Local`.
    #[inline]
    pub fn pin(&self) -> Guard {
        let guard = Guard { local: self };

        let guard_count = self.guard_count.get();
        self.guard_count.set(guard_count.checked_add(1).unwrap());

        if guard_count == 0 {
            // Loads the current local status. It's safe not to protect the access because no other
            // threads are modifying it.
            let local_status = unsafe { self.status.load(Ordering::Relaxed, unprotected()) };
            let local_flags = StatusFlags::from_bits_truncate(local_status.tag());
            debug_assert!(
                !local_flags.is_pinned(),
                "[Local::pin()] `self` should be unpinned"
            );

            // Loads the current global status. It's safe not to protect the load because we're not
            // accessing its contents.
            let mut global_status =
                unsafe { self.global().status.load(Ordering::Relaxed, unprotected()) };

            loop {
                let global_flags = StatusFlags::from_bits_truncate(global_status.tag());

                // Stores the local status as pinned at the epoch.
                let new_status =
                    local_status.with_tag(StatusFlags::new(true, global_flags.epoch()).bits());

                // Now we must store the new status into `self.status` and execute a `SeqCst` fence.
                // The fence makes sure that any future loads from `Atomic`s will not happen before
                // this store.
                if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
                    // HACK(stjepang): On x86 architectures there are two different ways of
                    // executing a `SeqCst` fence.
                    //
                    // 1. `atomic::fence(SeqCst)`, which compiles into a `mfence` instruction.
                    // 2. `_.compare_and_swap(_, _, SeqCst)`, which compiles into a `lock cmpxchg`
                    //    instruction.
                    //
                    // Both instructions have the effect of a full barrier, but benchmarks have
                    // shown that the second one makes pinning faster in this particular case.  It
                    // is not clear that this is permitted by the C++ memory model (SC fences work
                    // very differently from SC accesses), but experimental evidence suggests that
                    // this works fine.  Using inline assembly would be a viable (and correct)
                    // alternative, but alas, that is not possible on stable Rust.
                    self.status.swap(new_status, Ordering::SeqCst, &guard);

                    // We add a compiler fence to make it less likely for LLVM to do something wrong
                    // here.  Formally, this is not enough to get rid of data races; practically, it
                    // should go a long way.
                    atomic::compiler_fence(Ordering::SeqCst);
                } else {
                    self.status.store(new_status, Ordering::Relaxed);
                    atomic::fence(Ordering::SeqCst);
                }

                // Validates that the global status did not change.
                let global_status_validation =
                    unsafe { self.global().status.load(Ordering::Relaxed, unprotected()) };
                if global_status == global_status_validation {
                    break;
                }

                // Retries with a more recent value of global status.
                global_status = global_status_validation;
            }

            // Increment the pin counter.
            let count = self.pin_count.get();
            self.pin_count.set(count + Wrapping(1));

            // After every `PINNINGS_BETWEEN_COLLECT` try collecting some old garbage bags.
            if count.0 % Self::PINNINGS_BETWEEN_COLLECT == 0 {
                // If all old garbage bags are collected...
                if self.global().collect_inner(global_status, &guard) {
                    // After every `PINNINGS_BETWEEN_COLLECT` try advancing the global epoch.
                    if count.0 % Self::PINNINGS_BETWEEN_TRY_ADVANCE == 0 {
                        self.global().try_advance(&guard);
                    }
                }
            }
        }

        guard
    }

    /// Unpins the `Local`.
    #[inline]
    pub fn unpin(&self) {
        let guard_count = self.guard_count.get();
        self.guard_count.set(guard_count - 1);

        if guard_count == 1 {
            // Loads the old status, and defer to destroy the local HP summary.
            let local_status = unsafe { self.status.load(Ordering::Relaxed, unprotected()) };
            if !local_status.is_null() {
                // Creates a fake guard.
                let guard = Guard { local: self };

                unsafe {
                    guard.defer_destroy(local_status);
                }

                // Forgets the fake guard.
                mem::forget(guard);
            }

            // Creates a new local summary.
            let new_status = repeat_iter(|| self.hazards.make_summary(unsafe { unprotected() }))
                .map(|s| Owned::new(CachePadded::new(s)).into_shared(unsafe { unprotected() }))
                .unwrap_or_else(|| Shared::null())
                .with_tag(StatusFlags::new(false, 0).bits());

            // Stores the new status (unpinned).
            self.status.store(new_status, Ordering::Release);

            if self.handle_count.get() == 0 {
                self.finalize();
            }
        }
    }

    /// Unpins and then pins the `Local`.
    #[inline]
    pub fn repin(&self) {
        let guard_count = self.guard_count.get();

        // Update the local epoch only if there's only one guard.
        if guard_count == 1 {
            let local_status = unsafe { self.status.load(Ordering::Relaxed, unprotected()) };
            let global_status =
                unsafe { self.global().status.load(Ordering::Relaxed, unprotected()) };
            let local_flags = StatusFlags::from_bits_truncate(local_status.tag());
            let global_flags = StatusFlags::from_bits_truncate(global_status.tag());

            // Update the local epoch only if the global epoch is greater than the local epoch.
            if local_flags.epoch() != global_flags.epoch() {
                // Defers to destroy the old local HP summary.
                if !local_status.is_null() {
                    // Creates a fake guard.
                    let guard = Guard { local: self };

                    unsafe {
                        guard.defer_destroy(local_status);
                    }

                    // Forgets the fake guard.
                    mem::forget(guard);
                }

                // Creates a new local HP summary.
                let new_status =
                    repeat_iter(|| self.hazards.make_summary(unsafe { unprotected() }))
                        .map(|s| {
                            Owned::new(CachePadded::new(s)).into_shared(unsafe { unprotected() })
                        })
                        .unwrap_or_else(|| Shared::null())
                        .with_tag(StatusFlags::new(true, global_flags.epoch()).bits());

                // We store the new epoch with `Release` because we need to ensure any memory
                // accesses from the previous epoch do not leak into the new one.
                //
                // However, we don't need a following `SeqCst` fence, because it is safe for memory
                // accesses from the new epoch to be executed before updating the local epoch. At
                // worse, other threads will see the new epoch late and delay GC slightly.
                self.status.store(new_status, Ordering::Release);
            }
        }
    }

    /// Increments the handle count.
    #[inline]
    pub fn acquire_handle(&self) {
        let handle_count = self.handle_count.get();
        debug_assert!(handle_count >= 1);
        self.handle_count.set(handle_count + 1);
    }

    /// Decrements the handle count.
    #[inline]
    pub fn release_handle(&self) {
        let guard_count = self.guard_count.get();
        let handle_count = self.handle_count.get();
        debug_assert!(handle_count >= 1);
        self.handle_count.set(handle_count - 1);

        if guard_count == 0 && handle_count == 1 {
            self.finalize();
        }
    }

    /// Removes the `Local` from the global linked list.
    #[cold]
    fn finalize(&self) {
        debug_assert_eq!(self.guard_count.get(), 0);
        debug_assert_eq!(self.handle_count.get(), 0);

        unsafe {
            // Pin and move the local bag into the global queue. It's important that `push_bag`
            // doesn't defer destruction on any new garbage.
            let local_status = self.status.load(Ordering::Relaxed, unprotected());
            let local_flags = StatusFlags::from_bits_truncate(local_status.tag());
            self.global().push_bag(&mut *self.bag.get(), local_flags.epoch());

            debug_assert!(
                local_status.is_null(),
                "[Local::finalize()] `local_status` should be null",
            );

            // Take the reference to the `Global` out of this `Local`. Since we're not protected
            // by a guard at this time, it's crucial that the reference is read before marking the
            // `Local` as deleted.
            let collector: Collector = ptr::read(&*(*self.collector.get()));

            // Mark this node in the linked list as deleted.
            self.entry.delete();

            // Finally, drop the reference to the global. Note that this might be the last reference
            // to the `Global`. If so, the global data will be destroyed and all deferred functions
            // in its queue will be executed.
            drop(collector);
        }
    }
}

impl IsElement<Local> for Local {
    fn entry_of(local: &Local) -> &Entry {
        let entry_ptr = (local as *const Local as usize + offset_of!(Local, entry)) as *const Entry;
        unsafe { &*entry_ptr }
    }

    unsafe fn element_of(entry: &Entry) -> &Local {
        // offset_of! macro uses unsafe, but it's unnecessary in this context.
        #[allow(unused_unsafe)]
        let local_ptr = (entry as *const Entry as usize - offset_of!(Local, entry)) as *const Local;
        &*local_ptr
    }

    unsafe fn finalize(entry: &Entry, guard: &Guard) {
        guard.defer_destroy(Shared::from(Self::element_of(entry) as *const _));
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use deferred::Deferred;

    #[test]
    fn check_defer() {
        static FLAG: AtomicUsize = AtomicUsize::new(0);
        fn set() {
            FLAG.store(42, Ordering::Relaxed);
        }

        let d = Deferred::new(set);
        assert_eq!(FLAG.load(Ordering::Relaxed), 0);
        d.call();
        assert_eq!(FLAG.load(Ordering::Relaxed), 42);
    }
}
