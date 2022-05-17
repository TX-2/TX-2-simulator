use std::fmt::Debug;
use std::time::Duration;

use base::collections::pq::KeyedReversePriorityQueue;
use base::prelude::*;

#[derive(Debug)]
pub struct PollQueue {
    items: KeyedReversePriorityQueue<SequenceNumber, Duration>,
}

#[derive(Debug)]
pub enum PollQueueUpdateFailure {
    UnknownSequence(SequenceNumber),
}

impl PollQueue {
    pub fn new() -> PollQueue {
        PollQueue {
            items: KeyedReversePriorityQueue::new(),
        }
    }

    pub fn peek(&self) -> Option<(&SequenceNumber, &Duration)> {
        self.items.peek()
    }

    pub fn pop(&mut self) -> Option<(SequenceNumber, Duration)> {
        self.items.pop()
    }

    pub fn push(&mut self, key: SequenceNumber, priority: Duration) -> Option<Duration> {
        self.items.push(key, priority)
    }

    pub fn update(
        &mut self,
        key: SequenceNumber,
        priority: Duration,
    ) -> Result<Duration, PollQueueUpdateFailure> {
        match self.items.set_priority(&key, priority) {
            Ok(priority) => Ok(priority),
            Err(_) => Err(PollQueueUpdateFailure::UnknownSequence(key)),
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
