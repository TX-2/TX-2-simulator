//! Containers, including [`OneOrMore`].
use std::error::Error;
use std::fmt::{Display, Formatter};

/// Indicates  failure  of  an  attempt   to  create  an  instance  of
/// `OneOrMore<T>` when there are zero items to construct it from.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NoItems {}

impl Display for NoItems {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("cannot create an instance of OneOrMore from zero items")
    }
}

impl Error for NoItems {}

/// A container for at least one item.  As a convenience, we don't
/// implement methods that reduce the length of the container (so
/// that, for example, we don't have to implement a fallible
/// equivalent of `pop()`).  However, the container is mutable in the
/// sense that the items stored in it can be mutated.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OneOrMore<T> {
    head: T,
    tail: Vec<T>,
}

impl<T> OneOrMore<T> {
    /// Create an instance of `OneOrMore<T>` from a single `T`.
    pub fn new(head: T) -> OneOrMore<T> {
        OneOrMore::with_tail(head, Vec::new())
    }

    /// Create an instance of `OneOrMore<T>` from a single `T` value
    /// and zero or more additional `T` values.
    pub fn with_tail(head: T, tail: Vec<T>) -> OneOrMore<T> {
        OneOrMore { head, tail }
    }

    /// Return a reference to the first item.
    pub fn first(&self) -> &T {
        &self.head
    }

    /// Return a reference to the last item.
    pub fn last(&self) -> &T {
        match self.tail.last() {
            Some(b) => b,
            None => &self.head,
        }
    }

    /// Append an item.
    pub fn push(&mut self, item: T) {
        self.tail.push(item);
    }

    /// Return an iterator for the collection.
    pub fn iter(&self) -> OneOrMoreIter<'_, T> {
        OneOrMoreIter {
            inner: std::iter::once(&self.head).chain(self.tail.iter()),
        }
    }

    /// Convert the collection into an iterator over the items of the
    /// collection.
    pub fn into_iter(self) -> OneOrMoreIntoIter<T> {
        let Self { head, tail } = self;
        OneOrMoreIntoIter {
            inner: std::iter::once(head).chain(tail),
        }
    }

    /// Return a iterator for the collection which allows the items
    /// within it (but not the number of items) to be modified.
    pub fn iter_mut(&mut self) -> OneOrMoreIterMut<'_, T> {
        OneOrMoreIterMut {
            inner: std::iter::once(&mut self.head).chain(self.tail.iter_mut()),
        }
    }

    /// Return the number of items in the collection.
    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }

    /// Build an instance of `OneOrMore<T>` from a sequence of items,
    /// or fail (because there were no items).
    pub fn try_from_iter<I: Iterator<Item = T>>(mut it: I) -> Result<Self, NoItems> {
        match it.next() {
            Some(head) => Ok(Self {
                head,
                tail: it.collect(),
            }),
            _ => Err(NoItems {}),
        }
    }

    /// Append a (possibly empty) sequence of items.
    pub fn extend<I: Iterator<Item = T>>(&mut self, items: I) {
        self.tail.extend(items);
    }

    /// Attempt to convert an instance of `OneOrMore<T>` from a
    /// `Vec<T>`.  This fails if the vector is empty.
    pub fn try_from_vec(mut value: Vec<T>) -> Result<OneOrMore<T>, NoItems> {
        if value.is_empty() {
            Err(NoItems {})
        } else {
            let tail = value.split_off(1);
            Ok(OneOrMore::with_tail(
                value.pop().expect("known to be non-empty"),
                tail,
            ))
        }
    }

    /// Return a reference the head of the collection (i.e. the first
    /// item) and a reference to the remaining items.
    pub fn as_parts(&self) -> (&T, &Vec<T>) {
        (&self.head, &self.tail)
    }

    /// Create a non-empty collection by computing a mapping on the
    /// items on this collection.
    pub fn map<U, F: FnMut(&T) -> U>(&self, mut f: F) -> OneOrMore<U> {
        OneOrMore {
            head: f(&self.head),
            tail: self.tail.iter().map(f).collect(),
        }
    }

    /// Create a non-empty collection by computing a mapping on the
    /// items on this collection; this collection is dropped.
    pub fn into_map<U, F: FnMut(T) -> U>(self, mut f: F) -> OneOrMore<U> {
        OneOrMore {
            head: f(self.head),
            tail: self.tail.into_iter().map(f).collect(),
        }
    }
}

pub struct OneOrMoreIter<'a, T> {
    inner: std::iter::Chain<std::iter::Once<&'a T>, std::slice::Iter<'a, T>>,
}

impl<'a, T> Iterator for OneOrMoreIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

pub struct OneOrMoreIntoIter<T> {
    inner: std::iter::Chain<std::iter::Once<T>, <Vec<T> as IntoIterator>::IntoIter>,
}

impl<T> Iterator for OneOrMoreIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

pub struct OneOrMoreIterMut<'a, T> {
    inner: std::iter::Chain<std::iter::Once<&'a mut T>, std::slice::IterMut<'a, T>>,
}

impl<'a, T> Iterator for OneOrMoreIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<T> From<OneOrMore<T>> for Vec<T> {
    fn from(mut value: OneOrMore<T>) -> Self {
        let mut result = Vec::with_capacity(value.len());
        result.push(value.head);
        result.append(&mut value.tail);
        result
    }
}

impl<T: PartialEq<T>> PartialEq<Vec<T>> for OneOrMore<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        let mut other_it = other.iter();
        match other_it.next() {
            Some(first) => {
                if first != &self.head {
                    return false;
                }
                let mut self_it = self.tail.iter();
                // We don't want to use zip() here because we want our
                // comparison to fail when one iterator is shorter
                // than the other.
                loop {
                    match (self_it.next(), other_it.next()) {
                        (Some(mine), Some(theirs)) => {
                            if mine != theirs {
                                return false;
                            }
                        }
                        (None, Some(_)) | (Some(_), None) => {
                            return false;
                        }
                        (None, None) => {
                            return true;
                        }
                    }
                }
            }
            None => false,
        }
    }
}

#[cfg(test)]
mod one_or_more_tests {
    use super::{NoItems, OneOrMore};

    #[test]
    fn test_first() {
        let mut v: OneOrMore<u32> = OneOrMore::new(12);
        assert_eq!(v.first(), &12);
        v.push(8);
        assert_eq!(v.first(), &12);
    }

    #[test]
    fn test_last() {
        let v: OneOrMore<u32> = OneOrMore::new(200);
        assert_eq!(v.last(), &200);
    }

    #[test]
    fn test_push() {
        let mut v: OneOrMore<u32> = OneOrMore::new(1);
        assert_eq!(v.last(), &1);
        v.push(2);
        assert_eq!(v.last(), &2);
    }

    #[test]
    fn test_iter() {
        let mut v: OneOrMore<u32> = OneOrMore::new(1);
        v.push(2);
        let mut it = v.iter();
        assert_eq!(it.next(), Some(&1));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_into_iter() {
        let mut v: OneOrMore<i32> = OneOrMore::new(-1);
        v.push(-2);
        let mut it = v.into_iter();
        assert_eq!(it.next(), Some(-1));
        assert_eq!(it.next(), Some(-2));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_len() {
        let mut v: OneOrMore<u32> = OneOrMore::new(0);
        assert_eq!(v.len(), 1);
        v.push(0);
        assert_eq!(v.len(), 2);
    }

    #[test]
    fn test_try_from_iter_nonempty() {
        let input = [4];
        assert_eq!(
            OneOrMore::try_from_iter(input.iter()),
            Ok(OneOrMore {
                head: &4,
                tail: Vec::new()
            })
        );

        let input = [4, 8];
        assert_eq!(
            OneOrMore::try_from_iter(input.iter()),
            Ok(OneOrMore {
                head: &4,
                tail: vec![&8]
            })
        );
    }

    #[test]
    fn test_try_from_iter_empty() {
        let input: Vec<u8> = Vec::new();
        if let Ok(unexpected) = OneOrMore::try_from_iter(input.iter()) {
            panic!(
                "collecting from an empty iterator should fail, but instead we got {unexpected:?}"
            );
        }
    }

    #[test]
    fn test_iter_mut() {
        let mut v: OneOrMore<i32> = OneOrMore::try_from_iter([1, 2, 3, 4].into_iter())
            .expect("collection from non-empty sequence should succeed");
        for item in v.iter_mut() {
            *item = item.saturating_add(1);
        }
        let values: Vec<i32> = v.into_iter().collect();
        assert_eq!(values, vec![2, 3, 4, 5]);
    }

    #[test]
    fn test_extend() {
        let mut v: OneOrMore<i32> = OneOrMore::new(1);
        v.extend([2, 3].into_iter());
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn test_self_eq() {
        assert_eq!(OneOrMore::new(1), OneOrMore::new(1));
        assert_ne!(OneOrMore::new(1), OneOrMore::new(2));

        assert_eq!(
            OneOrMore::with_tail(1, vec![2]),
            OneOrMore::with_tail(1, vec![2])
        );
        assert_ne!(
            OneOrMore::with_tail(1, vec![2]),
            OneOrMore::with_tail(1, vec![2, 2])
        );
        assert_ne!(
            OneOrMore::with_tail(1, vec![2, 2]),
            OneOrMore::with_tail(1, vec![2])
        );
    }

    #[test]
    fn test_from_vec_to_option() {
        assert_eq!(Err(NoItems {}), OneOrMore::try_from_vec(Vec::<u64>::new()));
        assert_eq!(Ok(OneOrMore::new(2)), OneOrMore::try_from_vec(vec![2]));
        assert_eq!(
            Ok(OneOrMore::with_tail(10, vec![20])),
            OneOrMore::try_from_vec(vec![10, 20])
        );
    }

    #[test]
    fn test_map() {
        assert_eq!(
            OneOrMore::with_tail(1, vec![2]).map(|x| -x),
            OneOrMore::with_tail(-1, vec![-2])
        );
    }

    #[test]
    fn test_into_map() {
        assert_eq!(
            OneOrMore::with_tail(1, vec![2]).into_map(|x| -x),
            OneOrMore::with_tail(-1, vec![-2])
        );
    }
}
