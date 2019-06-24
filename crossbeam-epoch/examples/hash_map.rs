extern crate crossbeam_epoch as epoch;
extern crate crossbeam_utils as utils;
#[macro_use]
extern crate memoffset;

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::{Acquire, Relaxed, Release, SeqCst};

use epoch::sync::list::{Entry, IsElement, IterError, List};
use epoch::{Atomic, Guard, Owned, Shared};
use utils::thread::scope;

pub struct Node<K, V> {
    entry: Entry,
    key: K, // TODO: ManuallyDrop? since I'm using `ptr::read`
    value: Atomic<V>,
}

// TODO: SeqCst

/// Returns None if no entry with the key or null value
fn list_get<'g, 'a: 'g, K: Eq, V>(
    list: &'a List<Node<K, V>>,
    k: &K,
    guard: &'g Guard,
) -> Option<&'g V> {
    for node in list.iter(guard) {
        match node {
            Err(IterError::Stalled) => continue,
            Ok(node) => {
                if *k == node.key {
                    return unsafe { node.value.load(SeqCst, guard).as_ref() };
                }
            }
        }
    }
    None
}

fn list_find<'g, 'a: 'g, K: Eq, V>(
    list: &'a List<Node<K, V>>,
    k: &K,
    guard: &'g Guard,
) -> Option<&'g Node<K, V>> {
    for node in list.iter(guard) {
        match node {
            Err(IterError::Stalled) => continue,
            Ok(node) => {
                if *k == node.key {
                    return Some(&node);
                }
            }
        }
    }
    None
}

// returns old element
fn list_insert<K: Eq, V>(list: &List<Node<K, V>>, k: K, v: V) -> Option<V> {
    let guard = &epoch::pin();
    let mut k = k;
    let mut value = Atomic::new(v);
    loop {
        let snapshot = list.head().load(SeqCst, guard);
        match list_find(list, &k, guard) {
            Some(slot) => {
                let slot = &slot.value;
                let old = slot.load(SeqCst, guard);
                match unsafe { slot.compare_and_set(old, value.into_owned(), SeqCst, guard) } {
                    Ok(_) => {
                        return match unsafe { old.as_ref() } {
                            Some(old) => unsafe { Some(ptr::read(old)) },
                            None => None,
                        };
                    }
                    Err(e) => {
                        value = Atomic::from(e.new);
                        continue;
                    }
                }
            }
            None => {
                let node = Node {
                    entry: Entry::default(),
                    key: k,
                    value: value,
                };
                let new = Owned::new(node).into_shared(guard);
                unsafe {
                    if !list.insert_with_snapshot(snapshot, new, guard) {
                        let node = new.into_owned();
                        // TODO: probably wrong
                        value = ptr::read(&node.value);
                        k = ptr::read(&node.key);
                        continue;
                    }
                }
                return None;
            }
        }
    }
}

fn list_remove<K: Eq, V>(list: &List<Node<K, V>>, k: &K) -> Option<V> {
    let guard = &epoch::pin();
    loop {
        match list_find(list, &k, guard) {
            Some(slot) => {
                let value = &slot.value;
                let old = value.load(SeqCst, guard);
                match value.compare_and_set(old, Shared::null(), SeqCst, guard) {
                    Ok(_) => {
                        unsafe {
                            // TODO: hmmmmmmmmmmmmmmmmmmmmmmmmm
                            // double delete?
                            slot.entry.delete(guard);
                            return match old.as_ref() {
                                Some(old) => Some(ptr::read(old)),
                                None => None,
                            };
                        }
                    }
                    Err(_) => continue,
                }
            }
            None => return None,
        }
    }
}

impl<K, V> IsElement<Node<K, V>> for Node<K, V> {
    fn entry_of(node: &Node<K, V>) -> &Entry {
        let entry_ptr =
            (node as *const Node<K, V> as usize + offset_of!(Node<K, V>, entry)) as *const Entry;
        unsafe { &*entry_ptr }
    }

    unsafe fn element_of(entry: &Entry) -> &Node<K, V> {
        let node_ptr =
            (entry as *const Entry as usize - offset_of!(Node<K, V>, entry)) as *const Node<K, V>;
        &*node_ptr
    }

    unsafe fn finalize(entry: &Entry) {
        let node = Self::element_of(entry);
        drop(Owned::from_raw(
            node as *const Node<K, V> as *mut Node<K, V>,
        ));
    }
}

pub struct HashMap<K, V> {
    num_buckets: usize,
    buckets: Vec<List<Node<K, V>>>,
    // size: AtomicUsize, TODO
}

impl<K, V> HashMap<K, V>
where
    K: Eq + Hash,
{
    pub fn with_capacity(n: usize) -> Self {
        let mut b = Vec::with_capacity(n);
        for _ in 0..n {
            b.push(List::new());
        }
        HashMap {
            num_buckets: n,
            buckets: b,
        }
    }

    #[inline]
    fn hash(k: &K) -> usize {
        let mut s = DefaultHasher::new();
        k.hash(&mut s);
        s.finish() as usize
    }

    pub fn get<'g, 'a: 'g>(&'a self, k: &K, guard: &'g Guard) -> Option<&'g V> {
        let i = Self::hash(k) % self.num_buckets;
        list_get(&self.buckets[i], k, &guard)
    }

    pub fn insert(&self, k: K, v: V) -> Option<V> {
        let i = Self::hash(&k) % self.num_buckets;
        list_insert(&self.buckets[i], k, v)
    }

    pub fn remove(&self, k: &K) -> Option<V> {
        let i = Self::hash(&k) % self.num_buckets;
        list_remove(&self.buckets[i], k)
    }
}

impl<K, V> HashMap<K, V>
where
    K: std::fmt::Display + std::cmp::Ord,
    V: std::fmt::Debug,
{
    pub fn print(&self) {
        let guard = &epoch::pin();
        let mut lss = Vec::new();
        for b in &self.buckets {
            let mut ls = Vec::new();
            for n in b.iter(guard) {
                match n {
                    Err(IterError::Stalled) => {
                        ls.clear();
                        continue;
                    }
                    Ok(node) => {
                        ls.push((&node.key, node.value.load(SeqCst, guard)));
                    }
                }
            }
            lss.append(&mut ls);
        }
        lss.sort();
        for (k, v) in &lss {
            println!("{} |-> {:?}", k, unsafe {
                v.as_ref().map_or(None, |x| Some(x))
            });
        }
    }
}

impl<K, V> Drop for HashMap<K, V> {
    fn drop(&mut self) {
        let guard = &epoch::pin();
        for b in &self.buckets {
            for n in b.iter(guard) {
                match n {
                    Err(_) => continue,
                    Ok(n) => unsafe { n.entry.delete(guard) },
                }
            }
        }
    }
}

fn main() {
    let map = &HashMap::with_capacity(100);
    scope(|s| {
        for t in 0..100 {
            s.spawn(move |_| {
                for i in 0..1000 {
                    map.insert(i, (i, t));
                }
            });
        }
    })
    .unwrap();
    map.remove(&999);
    map.insert(999, (1, 100));
    map.print();
    // let guard = &epoch::pin();
}
