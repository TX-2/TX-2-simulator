use std::error::Error;
use std::fmt::{Display, Formatter};

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
/// equivalent of pop()).  However, the container is mutable in the
/// sense that the items stored in it can be mutated.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OneOrMore<T> {
    head: T,
    tail: Vec<T>,
}
impl<T> OneOrMore<T> {
    pub fn new(head: T) -> OneOrMore<T> {
        OneOrMore {
            head,
            tail: Vec::new(),
        }
    }

    pub fn first(&self) -> &T {
        &self.head
    }

    pub fn last(&self) -> &T {
        match self.tail.last() {
            Some(b) => b,
            None => &self.head,
        }
    }

    pub fn push(&mut self, item: T) {
        self.tail.push(item);
    }

    pub fn iter(&self) -> OneOrMoreIter<T> {
        OneOrMoreIter {
            inner: std::iter::once(&self.head).chain(self.tail.iter()),
        }
    }

    pub fn into_iter(self) -> OneOrMoreIntoIter<T> {
        let Self { head, tail } = self;
        OneOrMoreIntoIter {
            inner: std::iter::once(head).chain(tail),
        }
    }

    pub fn iter_mut(&mut self) -> OneOrMoreIterMut<T> {
        OneOrMoreIterMut {
            inner: std::iter::once(&mut self.head).chain(self.tail.iter_mut()),
        }
    }

    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }

    pub fn try_from_iter<I: Iterator<Item = T>>(mut it: I) -> Result<Self, NoItems> {
        if let Some(head) = it.next() {
            Ok(Self {
                head,
                tail: it.collect(),
            })
        } else {
            Err(NoItems {})
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

#[cfg(test)]
mod one_or_more_tests {
    use super::OneOrMore;

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
}
