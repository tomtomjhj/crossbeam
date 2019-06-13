use std::mem::ManuallyDrop;
use std::ptr;
use std::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use atomic::{Atomic, Owned};
use guard::{unprotected, Guard};

/// 's lock-free stack.
///
/// Usable with any number of producers and consumers.
#[derive(Debug)]
pub struct Stack<T> {
    head: Atomic<Node<T>>,
}

#[derive(Debug)]
struct Node<T> {
    data: ManuallyDrop<T>,
    next: Atomic<Node<T>>,
}

impl<T> Stack<T> {
    /// Creates a new, empty stack.
    pub fn new() -> Stack<T> {
        Stack {
            head: Atomic::null(),
        }
    }

    /// Pushes a value on top of the stack.
    pub fn push(&self, t: T, guard: &Guard) {
        let mut n = Owned::new(Node {
            data: ManuallyDrop::new(t),
            next: Atomic::null(),
        });

        loop {
            let head = self.head.load(Relaxed, guard);
            n.next.store(head, Relaxed);

            match self.head.compare_and_set(head, n, Release, guard) {
                Ok(_) => break,
                Err(e) => n = e.new,
            }
        }
    }

    /// Attempts to pop the top element from the stack.
    ///
    /// Returns `None` if the stack is empty.
    pub fn try_pop(&self, guard: &Guard) -> Option<T> {
        loop {
            let head = self.head.load(Acquire, guard);

            match unsafe { head.as_ref() } {
                Some(h) => {
                    let next = h.next.load(Relaxed, guard);

                    if self
                        .head
                        .compare_and_set(head, next, Release, guard)
                        .is_ok()
                    {
                        unsafe {
                            let data = ptr::read(&(*h).data);
                            guard.defer_destroy(head);
                            return Some(ManuallyDrop::into_inner(data));
                        }
                    }
                }
                None => return None,
            }
        }
    }
}

impl<T> Drop for Stack<T> {
    fn drop(&mut self) {
        let guard = unsafe { unprotected() };
        while self.try_pop(guard).is_some() {}
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crossbeam_utils::thread;
    use pin;

    #[test]
    fn smoke() {
        let stack = Stack::new();

        thread::scope(|scope| {
            for _ in 0..10 {
                scope.spawn(|_| {
                    for i in 0..10_000 {
                        let guard = pin();
                        stack.push(i, &guard);
                        assert!(stack.try_pop(&guard).is_some());
                    }
                });
            }
        })
        .unwrap();

        let guard = pin();
        assert!(stack.try_pop(&guard).is_none());
    }
}
