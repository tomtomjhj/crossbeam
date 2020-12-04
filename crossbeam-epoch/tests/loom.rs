#![cfg(feature = "check-loom")]

use crossbeam_epoch as epoch;

use epoch::*;
use epoch::{Atomic, Owned};
use loom::sync::atomic::AtomicUsize;
use loom::sync::atomic::Ordering::{self, Acquire, Relaxed, Release};
use loom::thread::spawn;
use std::mem::ManuallyDrop;
use std::ptr;
use std::sync::Arc;

#[test]
fn it_works() {
    loom::model(|| {
        let collector = Collector::new();
        let item: Atomic<String> = Atomic::from(Owned::new(String::from("boom")));
        let item2 = item.clone();
        let collector2 = collector.clone();
        let guard = collector.register().pin();

        let jh = loom::thread::spawn(move || {
            let guard = collector2.register().pin();
            guard.defer(move || {
                // this isn't really safe, since other threads may still have pointers to the
                // value, but in this limited test scenario it's okay, since we know the test won't
                // access item after all the pins are released.
                let mut item = unsafe { item2.into_owned() };
                // mutate it as a second measure to make sure the assert_eq below would fail
                item.retain(|c| c == 'o');
                drop(item);
            });
        });

        let item = item.load(Ordering::SeqCst, &guard);
        // we pinned strictly before the call to defer_destroy,
        // so item cannot have been dropped yet
        assert_eq!(*unsafe { item.deref() }, "boom");
        drop(guard);

        jh.join().unwrap();

        drop(collector);
    })
}

#[test]
fn treiber_stack() {
    // this is mostly a copy-paste from the example
    #[derive(Debug)]
    pub struct TreiberStack<T> {
        head: Atomic<Node<T>>,
    }

    #[derive(Debug)]
    struct Node<T> {
        data: ManuallyDrop<T>,
        next: Atomic<Node<T>>,
    }

    impl<T> TreiberStack<T> {
        pub fn new() -> TreiberStack<T> {
            TreiberStack {
                head: Atomic::null(),
            }
        }

        pub fn push(&self, t: T) {
            let mut n = Owned::new(Node {
                data: ManuallyDrop::new(t),
                next: Atomic::null(),
            });

            let guard = epoch::pin();

            loop {
                let head = self.head.load(Relaxed, &guard);
                n.next.store(head, Relaxed);

                match self.head.compare_and_set(head, n, Release, &guard) {
                    Ok(_) => break,
                    Err(e) => n = e.new,
                }
            }
        }

        pub fn pop(&self) -> Option<T> {
            let guard = epoch::pin();
            loop {
                let head = self.head.load(Acquire, &guard);

                match unsafe { head.as_ref() } {
                    Some(h) => {
                        let next = h.next.load(Relaxed, &guard);

                        if self
                            .head
                            .compare_and_set(head, next, Relaxed, &guard)
                            .is_ok()
                        {
                            unsafe {
                                guard.defer_destroy(head);
                                return Some(ManuallyDrop::into_inner(ptr::read(&(*h).data)));
                            }
                        }
                    }
                    None => return None,
                }
            }
        }

        pub fn is_empty(&self) -> bool {
            let guard = epoch::pin();
            self.head.load(Acquire, &guard).is_null()
        }
    }

    impl<T> Drop for TreiberStack<T> {
        fn drop(&mut self) {
            while self.pop().is_some() {}
        }
    }

    loom::model(|| {
        let stack1 = Arc::new(TreiberStack::new());
        let stack2 = Arc::clone(&stack1);

        // use 5 since it's greater than the 4 used for the sanitize feature
        let jh = spawn(move || {
            for i in 0..5 {
                stack2.push(i);
                assert!(stack2.pop().is_some());
            }
        });

        for i in 0..5 {
            stack1.push(i);
            assert!(stack1.pop().is_some());
        }

        jh.join().unwrap();
        assert!(stack1.pop().is_none());
        assert!(stack1.is_empty());
    });
}
