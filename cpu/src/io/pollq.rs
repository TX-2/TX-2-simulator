use std::cmp::Ordering;
use std::time::Duration;

use keyed_priority_queue::KeyedPriorityQueue;

use base::prelude::*;

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
    assert!(!(ReverseOrdered::from(1) > ReverseOrdered::from(0)));
}

#[derive(Debug)]
pub struct PollQueue {
    items: KeyedPriorityQueue<SequenceNumber, ReverseOrdered<Duration>>,
}

impl PollQueue {
    pub fn new() -> PollQueue {
        PollQueue {
            items: KeyedPriorityQueue::new(),
        }
    }

    pub fn peek(&self) -> Option<(&SequenceNumber, &Duration)> {
        self.items.peek().map(|(k, p)| (k, &p.inner))
    }

    pub fn pop(&mut self) -> Option<(SequenceNumber, Duration)> {
        self.items.pop().map(|(k, p)| (k, p.inner))
    }

    pub fn push(&mut self, key: SequenceNumber, priority: Duration) -> Option<Duration> {
        match self.items.push(key, ReverseOrdered::from(priority)) {
            None => None,
            Some(rd) => Some(rd.inner),
        }
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

#[test]
fn test_pollqueue_empty() {
    let mut q = PollQueue::new();
    assert!(q.is_empty());
    assert_eq!(0, q.len());
    assert_eq!(q.peek(), None);
    assert_eq!(q.pop(), None);
}

#[test]
fn test_pollqueue_repeat_push() {
    let mut q = PollQueue::new();
    assert_eq!(
        q.push(SequenceNumber::ZERO, Duration::from_micros(200)),
        None
    );
    assert_eq!(
        q.push(SequenceNumber::ZERO, Duration::from_micros(400)),
        Some(Duration::from_micros(200))
    );
    assert_eq!(
        q.push(SequenceNumber::ZERO, Duration::from_micros(300)),
        Some(Duration::from_micros(400))
    );
    assert_eq!(
        q.pop(),
        Some((SequenceNumber::ZERO, Duration::from_micros(300)))
    );
    assert!(q.is_empty());
}
