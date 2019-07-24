use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::sync::atomic::{fence, AtomicUsize, Ordering};

use atomic::{Owned, Pointer, Shared};
use bloom_filter::BloomFilter;
use guard::{unprotected, Guard};
use internal::Local;
use sync::list::{repeat_iter, Entry, IsElement, Iter as ListIter, IterError, List};
use tag::*;

/// Node in a linked list that represents a finite set of hazard pointers.
#[derive(Debug)]
pub struct HazardNode {
    /// The metadata for intrusive linked list.
    entry: Entry,

    /// The bitmap that represents the validity of elements in the array.
    valid_bits: AtomicUsize,

    /// The array of elements.
    elements: [AtomicUsize; HazardNode::SIZE],
}

impl IsElement<HazardNode> for HazardNode {
    fn entry_of(local: &HazardNode) -> &Entry {
        let entry_ptr =
            (local as *const HazardNode as usize + offset_of!(HazardNode, entry)) as *const Entry;
        unsafe { &*entry_ptr }
    }

    unsafe fn element_of(entry: &Entry) -> &HazardNode {
        // offset_of! macro uses unsafe, but it's unnecessary in this context.
        #[allow(unused_unsafe)]
        let node_ptr =
            (entry as *const Entry as usize - offset_of!(HazardNode, entry)) as *const HazardNode;
        &*node_ptr
    }

    unsafe fn finalize(entry: &Entry, guard: &Guard) {
        guard.defer_destroy(Shared::from(Self::element_of(entry) as *const _));
    }
}

impl HazardNode {
    /// The number of `AtomicUsize` in a node.
    ///
    /// The value is chosen so as to fit `HazardNode` in two cachelines.  Indeed, two cachelines (128
    /// bytes) are sufficient for (1) the "next" pointer for linked list, (2) valid bits, and (3) 14
    /// elements.
    ///
    /// Once the const generics are stabilized (https://github.com/rust-lang/rust/issues/44580), it
    /// can be a type parameter instead of a constant.
    const SIZE: usize = 14;

    pub fn new() -> Self {
        // Valid bits should be fit in a single word.
        const_assert!(HazardNode::SIZE <= 8 * mem::size_of::<usize>());

        Self {
            entry: Default::default(),
            valid_bits: Default::default(),
            elements: Default::default(),
        }
    }

    /// Acquires a value slot.
    ///
    /// # Safety
    ///
    /// The caller should be the "owner" of this node.
    #[inline]
    pub unsafe fn acquire(&self, data: usize) -> Option<usize> {
        let valid_bits = self.valid_bits.load(Ordering::Relaxed);
        let index = (!valid_bits).trailing_zeros() as usize;

        if index >= HazardNode::SIZE {
            return None;
        }

        self.valid_bits
            .store(valid_bits | (1 << index), Ordering::Relaxed);
        self.elements[index].store(data, Ordering::Relaxed);
        Some(index)
    }

    /// Releases a value slot, and returns whether the node becomes empty.
    ///
    /// # Safety
    ///
    /// The caller should be the "owner" of this node.
    #[inline]
    pub unsafe fn release(&self, index: usize) -> bool {
        let valid_bits = self.valid_bits.load(Ordering::Relaxed);
        let valid_bits = valid_bits & !(1 << index);
        fence(Ordering::Release);
        self.valid_bits.store(valid_bits, Ordering::Relaxed);
        self.elements[index].store(0, Ordering::Relaxed);

        valid_bits == 0
    }

    /// Updates a value slot.
    #[inline]
    pub unsafe fn update(&self, index: usize, data: usize, ord: Ordering) {
        self.elements[index].store(data, ord);
    }

    /// Returns an iterator for values.
    pub fn iter(&self) -> HazardNodeIter {
        HazardNodeIter {
            valid_bits: self.valid_bits.load(Ordering::Relaxed),
            set: self as *const _,
        }
    }
}

/// Iterator for the values in a [`HazardNode`].
///
/// [`HazardNode`]: struct.HazardNode.html
#[derive(Debug)]
pub struct HazardNodeIter {
    valid_bits: usize,
    set: *const HazardNode,
}

impl HazardNodeIter {
    fn empty() -> Self {
        Self {
            valid_bits: 0,
            set: ptr::null(),
        }
    }
}

impl Iterator for HazardNodeIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let index = self.valid_bits.trailing_zeros() as usize;

            if index >= HazardNode::SIZE {
                return None;
            }

            self.valid_bits &= !(1 << index);
            let value = unsafe { ((*self.set).elements)[index].load(Ordering::Acquire) };

            if value != 0 {
                return Some(value);
            }
        }
    }
}

/// Set of hazard pointers represented as a linked list.
#[derive(Debug)]
pub struct HazardSet {
    pred: UnsafeCell<Shield<HazardNode>>,
    curr: UnsafeCell<Shield<HazardNode>>,
    list: List<HazardNode>,
}

impl Drop for HazardSet {
    fn drop(&mut self) {
        unsafe {
            let guard = unprotected();

            for node in self
                .list
                .iter(&mut *self.pred.get(), &mut *self.curr.get(), guard)
                .unwrap()
            {
                let node = &*(node.unwrap());
                node.entry.delete();
            }
        }
    }
}

impl HazardSet {
    /// Creates a new hazard set.
    pub fn new() -> Self {
        unsafe {
            let guard = unprotected();

            let node = Owned::new(HazardNode::new());
            let index1 = node.acquire(0).unwrap();
            let index2 = node.acquire(0).unwrap();
            let node = node.into_shared(guard);

            let list = List::new();
            list.insert(node);

            Self {
                pred: UnsafeCell::new(Shield::from_raw(node.as_raw(), index1)),
                curr: UnsafeCell::new(Shield::from_raw(node.as_raw(), index2)),
                list,
            }
        }
    }

    /// Creates an iterator over the hazard set.
    #[must_use]
    pub fn iter<'g>(
        &'g self,
        pred: &'g mut Shield<HazardNode>,
        curr: &'g mut Shield<HazardNode>,
        guard: &'g Guard,
    ) -> Result<HazardSetIter<'g>, ShieldError> {
        Ok(HazardSetIter {
            list_iter: self.list.iter(pred, curr, guard)?,
            node_iter: HazardNodeIter::empty(),
        })
    }

    unsafe fn acquire_inner(
        &self,
        data: usize,
        guard: &Guard,
    ) -> Result<(*const HazardNode, usize), IterError> {
        for node in self
            .list
            .iter(&mut *self.pred.get(), &mut *self.curr.get(), guard)
            .map_err(|e| IterError::ShieldError(e))?
        {
            let node = node?;
            if let Some(index) = (*node).acquire(data) {
                return Ok((node, index));
            }
        }

        let new = HazardNode::new();
        let index = new.acquire(data).unwrap();
        let new = Owned::new(HazardNode::new()).into_shared(guard);
        self.list.insert(new);
        Ok((new.as_raw(), index))
    }

    /// Acquires a hazard pointer slot in the hazard set.
    ///
    /// # Safety
    ///
    /// The caller should be the "owner" of this set.
    #[must_use]
    pub unsafe fn acquire(
        &self,
        data: usize,
        guard: &Guard,
    ) -> Result<(*const HazardNode, usize), ShieldError> {
        repeat_iter(|| self.acquire_inner(data, guard))
    }

    /// Creates an approximate summary of the hazard set.
    #[inline]
    pub fn make_summary(&self, guard: &Guard) -> Result<Option<BloomFilter>, IterError> {
        let mut visited = false;
        let mut filter = BloomFilter::new();

        let mut pred = Shield::null(guard).map_err(|e| IterError::ShieldError(e))?;
        let mut curr = Shield::null(guard).map_err(|e| IterError::ShieldError(e))?;

        for hazard in self
            .iter(&mut pred, &mut curr, guard)
            .map_err(|e| IterError::ShieldError(e))?
        {
            filter.insert(hazard?);
            visited = true;
        }
        Ok(if visited { Some(filter) } else { None })
    }
}

/// Iterator for the values in a [`HazardSet`].
///
/// [`HazardSet`]: struct.HazardSet.html
#[derive(Debug)]
pub struct HazardSetIter<'g> {
    list_iter: ListIter<'g, HazardNode, HazardNode>,
    node_iter: HazardNodeIter,
}

impl<'g> Iterator for HazardSetIter<'g> {
    type Item = Result<usize, IterError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(result) = self.node_iter.next() {
                return Some(Ok(result));
            }

            let result = self.list_iter.next()?;
            match result {
                Ok(node) => self.node_iter = unsafe { (*node).iter() },
                Err(e) => return Some(Err(e)),
            }
        }
    }
}

/// TODO
#[derive(Debug, PartialEq, Eq)]
pub enum ShieldError {
    /// TODO
    Ejected,
}

/// RAII type for hazard pointers to shared objects.
#[derive(Debug)]
pub struct Shield<T> {
    pub(crate) data: usize,
    pub(crate) local: *const Local,
    pub(crate) node: *const HazardNode,
    pub(crate) index: usize,
    pub(crate) _marker: PhantomData<*const T>, // !Sync + !Send
}

impl<T> Drop for Shield<T> {
    fn drop(&mut self) {
        unsafe {
            if let Some(node) = self.node.as_ref() {
                if node.release(self.index) {
                    // The hazard node becomes empty. Deletes it.
                    HazardNode::entry_of(node).delete();
                }
            }

            if let Some(local) = self.local.as_ref() {
                local.release_handle();
            }
        }
    }
}

impl<T> Shield<T> {
    /// Creates a new shield.
    ///
    /// If this method is called from an [`unprotected`] guard, it returns a [`Shield`] that is not
    /// actually protecting the pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(777);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Creates a shield to the heap-allocated object.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// // Even though the guard is dropped, you can still dereference the shield and print the
    /// // value:
    /// if let Some(num) = unsafe { shield.as_ref() } {
    ///     println!("The number is {}.", num);
    /// }
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    /// [`Shield`]: struct.Shield.html
    #[must_use]
    pub fn new<'g>(ptr: Shared<'g, T>, guard: &Guard) -> Result<Self, ShieldError> {
        let data = ptr.into_usize();

        if let Some(local) = unsafe { guard.local.as_ref() } {
            // Acquire a handle so that the underlying thread-local storage is not deallocated.
            local.acquire_handle();

            let (node, index) =
                unsafe { local.hazards.acquire(data_with_tag::<T>(data, 0), guard)? };

            Ok(Self {
                data,
                local,
                node,
                index,
                _marker: PhantomData,
            })
        } else {
            Ok(Self {
                data,
                local: ptr::null(),
                node: ptr::null(),
                index: 0,
                _marker: PhantomData,
            })
        }
    }

    /// Creates a new null shield.
    ///
    /// See [`Shield::new`] for more details.
    ///
    /// [`Shield::new`]: struct.Shield.html#method.new
    #[must_use]
    pub fn null<'g>(guard: &Guard) -> Result<Self, ShieldError> {
        Self::new(Shared::null(), guard)
    }

    pub(crate) unsafe fn from_raw(node: *const HazardNode, index: usize) -> Self {
        Self {
            data: 0,
            local: ptr::null(),
            node,
            index,
            _marker: PhantomData,
        }
    }

    /// Converts the pointer to a raw pointer (without the tag).
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Owned, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let o = Owned::new(1234);
    /// let raw = &*o as *const _;
    /// let a = Atomic::from(o);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a new shield.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// assert_eq!(shield.as_raw(), raw);
    /// ```
    pub fn as_raw(&self) -> *const T {
        let (raw, _) = decompose_data::<T>(self.data);
        raw
    }

    /// Dereferences the shield.
    ///
    /// # Safety
    ///
    /// Dereferencing a pointer is unsafe because it could be pointing to invalid memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shared, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(1234);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a new shield.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// unsafe {
    ///     assert_eq!(shield.deref(), &1234);
    /// }
    /// ```
    pub unsafe fn deref(&self) -> &T {
        &*self.as_raw()
    }

    /// Converts the pointer to a reference.
    ///
    /// Returns `None` if the pointer is null, or else a reference to the object wrapped in `Some`.
    ///
    /// # Safety
    ///
    /// Dereferencing a pointer is unsafe because it could be pointing to invalid memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shared, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(1234);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a new shield.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// unsafe {
    ///     assert_eq!(shield.as_ref(), Some(&1234));
    /// }
    /// ```
    pub unsafe fn as_ref(&self) -> Option<&T> {
        self.as_raw().as_ref()
    }

    /// Returns the tag stored within the shield.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shared, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(1234);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a new shield.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// unsafe {
    ///     assert_eq!(shield.tag(), 0);
    /// }
    /// ```
    pub fn tag(&self) -> usize {
        let (_, tag) = decompose_data::<T>(self.data);
        tag
    }

    /// Creates a [`Shared`] pointer to the inner hazard pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shared, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(1234);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a new shield.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// unsafe {
    ///     assert_eq!(shield.deref(), &1234);
    /// }
    /// ```
    ///
    /// [`Shared`]: struct.Shared.html
    pub fn shared<'s>(&'s self) -> Shared<'s, T> {
        unsafe { Shared::from_usize(self.data) }
    }

    /// Defends a hazard pointer.
    ///
    /// This method registers a shared pointer as hazardous so that other threads will not destroy
    /// the pointer, and returns a [`Shield`] pointer as a handle for the registration.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shared, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(777);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a new shield.
    /// let mut shield = Shield::null(&guard).unwrap();
    ///
    /// // Defend the heap-allocated object.
    /// shield.defend(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// // Even though the guard is dropped, you can still dereference the shield and print the
    /// // value:
    /// if let Some(num) = unsafe { shield.as_ref() } {
    ///     println!("The number is {}.", num);
    /// }
    /// ```
    ///
    /// [`Shield`]: struct.Shield.html
    #[must_use]
    pub fn defend<'g>(&mut self, ptr: Shared<'g, T>, guard: &'g Guard) -> Result<(), ShieldError> {
        let data = ptr.into_usize();
        self.data = data;
        unsafe {
            if let Some(node) = self.node.as_ref() {
                node.update(self.index, data_with_tag::<T>(data, 0), Ordering::Relaxed);

                if let Some(local) = self.local.as_ref() {
                    // Ensures `local` is not ejected.
                    if let Err(e) = local.get_epoch(guard) {
                        self.data = 0;
                        node.update(self.index, 0, Ordering::Release);
                        return Err(e);
                    }
                }
            }
        }

        Ok(())
    }

    /// Releases the inner hazard pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_epoch::{self as epoch, Atomic, Shared, Shield};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// // Create a heap-allocated number.
    /// let a = Atomic::new(777);
    ///
    /// // Pin the current thread.
    /// let guard = epoch::pin();
    ///
    /// // Create a shield to the heap-allocated object.
    /// let mut shield = Shield::new(a.load(SeqCst, &guard), &guard).unwrap();
    ///
    /// // Releases the shield.
    /// shield.release();
    ///
    /// // Drop the guard.
    /// drop(guard);
    ///
    /// assert!(shield.shared().is_null());
    /// ```
    ///
    /// [`Shield`]: struct.Shield.html
    pub fn release(&mut self) {
        self.data = 0;
        unsafe {
            if let Some(node) = self.node.as_ref() {
                node.update(self.index, 0, Ordering::Release);
            }
        }
    }
}
