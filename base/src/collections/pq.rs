use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::hash::Hash;

use keyed_priority_queue::KeyedPriorityQueue;

#[derive(Debug)]
struct ReverseOrdered<T> {
    inner: T,
}

impl<T> From<T> for ReverseOrdered<T> {
    fn from(inner: T) -> ReverseOrdered<T> {
        ReverseOrdered { inner }
    }
}

impl<T: Ord> PartialOrd for ReverseOrdered<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Eq> Eq for ReverseOrdered<T> {}

impl<T: Eq> PartialEq for ReverseOrdered<T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<T: Ord> Ord for ReverseOrdered<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.inner.cmp(&other.inner) {
            Ordering::Less => Ordering::Greater,
            Ordering::Equal => Ordering::Equal,
            Ordering::Greater => Ordering::Less,
        }
    }
}

#[test]
fn test_reverse_order() {
    assert_eq!(ReverseOrdered::from(1), ReverseOrdered::from(1));
    assert_ne!(ReverseOrdered::from(1), ReverseOrdered::from(0));
    assert!(ReverseOrdered::from(1) < ReverseOrdered::from(0));
    assert_ne!(ReverseOrdered::from(1), ReverseOrdered::from(0));
    assert!(ReverseOrdered::from(1) <= ReverseOrdered::from(0));
}

pub struct KeyedReversePriorityQueueUnknownKeyError {}

pub struct KeyedReversePriorityQueue<K: Hash + Eq + Ord, P: Ord> {
    items: KeyedPriorityQueue<K, ReverseOrdered<P>>,
}

impl<K, P> KeyedReversePriorityQueue<K, P>
where
    K: Hash + Eq + Ord,
    P: Ord,
{
    pub fn new() -> KeyedReversePriorityQueue<K, P> {
        KeyedReversePriorityQueue {
            items: KeyedPriorityQueue::<K, ReverseOrdered<P>>::new(),
        }
    }

    pub fn peek(&self) -> Option<(&K, &P)> {
        self.items.peek().map(|(k, p)| (k, &p.inner))
    }

    pub fn pop(&mut self) -> Option<(K, P)> {
        self.items.pop().map(|(k, p)| (k, p.inner))
    }

    pub fn push(&mut self, key: K, priority: P) -> Option<P> {
        self.items
            .push(key, ReverseOrdered::from(priority))
            .map(|rd| rd.inner)
    }

    /// Update the priority of a item (identified by `key`) in the
    /// priority queue.
    ///
    /// # Errors
    ///
    /// Err(KeyedReversePriorityQueue) is returned when the indicated
    /// key is not present.
    pub fn set_priority(
        &mut self,
        key: &K,
        priority: P,
    ) -> Result<P, KeyedReversePriorityQueueUnknownKeyError> {
        match self.items.set_priority(key, ReverseOrdered::from(priority)) {
            Ok(priority) => Ok(priority.inner),
            Err(_) => Err(KeyedReversePriorityQueueUnknownKeyError {}),
        }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<K, P> Default for KeyedReversePriorityQueue<K, P>
where
    K: Hash + Eq + Ord,
    P: Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P> Debug for KeyedReversePriorityQueue<K, P>
where
    K: Hash + Eq + Ord + Debug,
    P: Ord + Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyedReversePriorityQueue")
            .field("items", &self.items)
            .finish()
    }
}

#[test]
fn test_empty() {
    let mut q: KeyedReversePriorityQueue<usize, usize> = KeyedReversePriorityQueue::default();
    assert!(q.is_empty());
    assert_eq!(0, q.len());
    assert_eq!(q.peek(), None);
    assert_eq!(q.pop(), None);
}

#[test]
fn test_nonempty() {
    let mut q: KeyedReversePriorityQueue<String, String> = KeyedReversePriorityQueue::new();
    assert!(q.is_empty());
    assert_eq!(
        q.push(
            "Muztagh Tower".to_string(),
            "Joe Brown, Ian McNaught-Davis".to_string()
        ),
        None
    );
    assert!(!q.is_empty());
}

#[test]
fn test_repeat_push() {
    let mut q: KeyedReversePriorityQueue<usize, char> = KeyedReversePriorityQueue::new();
    assert_eq!(q.push(0, '2'), None);
    assert_eq!(q.push(0, '4'), Some('2'));
    assert_eq!(q.push(0, '3'), Some('4'));
    assert_eq!(q.pop(), Some((0, '3')));
    assert!(q.is_empty());
}

#[test]
fn test_ordering() {
    let mut q: KeyedReversePriorityQueue<usize, char> = KeyedReversePriorityQueue::new();
    assert_eq!(q.push(0, '2'), None);
    assert_eq!(q.push(1, '8'), None);
    assert_eq!(q.pop(), Some((0, '2')));
    assert_eq!(q.pop(), Some((1, '8')));
    assert!(q.is_empty());

    // Now push them in the opposite order to prove that pop order
    // depends on priority, not insertion order.
    assert_eq!(q.push(1, '8'), None);
    assert_eq!(q.push(0, '2'), None);
    assert_eq!(q.pop(), Some((0, '2')));
    assert_eq!(q.pop(), Some((1, '8')));
    assert!(q.is_empty());
}
