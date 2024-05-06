use std::fmt::Debug;
use std::time::Duration;

use tracing::{event, Level};

use base::collections::pq::KeyedReversePriorityQueue;
use base::prelude::*;

#[derive(Debug)]
pub(crate) struct PollQueue {
    items: KeyedReversePriorityQueue<SequenceNumber, Duration>,
}

#[derive(Debug)]
pub(crate) enum PollQueueUpdateFailure {
    // UnknownSequence rises when we try to update the poll time for a
    // sequence with no attached hardware.  This is a normal thing for
    // software-only sequences.
    UnknownSequence(SequenceNumber),
}

impl PollQueue {
    pub(crate) fn new() -> PollQueue {
        PollQueue {
            items: KeyedReversePriorityQueue::new(),
        }
    }

    pub(crate) fn peek(&self) -> Option<(&SequenceNumber, &Duration)> {
        self.items.peek()
    }

    pub(crate) fn pop(&mut self) -> Option<(SequenceNumber, Duration)> {
        self.items.pop()
    }

    pub(crate) fn push(&mut self, key: SequenceNumber, priority: Duration) -> Option<Duration> {
        let old_pri = self.items.push(key, priority);
        if let Some(prev) = old_pri {
            if prev < priority {
                event!(
                    Level::WARN,
                    "unit {:o} poll time pushed back from {:?} to {:?}",
                    key,
                    prev,
                    priority
                );
            }
        }
        old_pri
    }

    pub(crate) fn update(
        &mut self,
        key: SequenceNumber,
        priority: Duration,
    ) -> Result<Duration, PollQueueUpdateFailure> {
        match self.items.set_priority(&key, priority) {
            Ok(old_pri) => {
                if old_pri < priority {
                    event!(
                        Level::WARN,
                        "unit {:o} poll time pushed back from {:?} to {:?}",
                        key,
                        old_pri,
                        priority
                    );
                }
                Ok(old_pri)
            }
            Err(_) => Err(PollQueueUpdateFailure::UnknownSequence(key)),
        }
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.items.len()
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
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
