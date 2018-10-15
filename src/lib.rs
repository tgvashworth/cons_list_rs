use std::iter::{IntoIterator, Iterator};
use std::ops::Index;
use std::rc::Rc;

/// An immutable linked-list data structure.
///
/// # Examples
///
/// ```
/// use std::rc::Rc;
/// use cons_list_rs::List::{Cons, Nil};
/// let list = Cons("a", Rc::new(Cons("b", Rc::new(Nil))));
/// ```
#[derive(Debug)]
pub enum List<T> {
    Cons(T, Rc<List<T>>),
    Nil,
}

use List::{Cons, Nil};

impl<T> List<T> {
    /// Get `Some(x)`, the nth value of the list, or None.
    pub fn nth(&self, n: usize) -> Option<&T> {
        match self {
            Nil => None,
            Cons(v, tail) => if n == 0 {
                Some(v)
            } else {
                tail.nth(n - 1)
            },
        }
    }

    /// Get the length of the list. The `Nil` list is empty.
    pub fn len(&self) -> usize {
        match self {
            Nil => 0,
            Cons(_, tail) => 1 + tail.len(),
        }
    }

    /// Get an `Iter` over this list.
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }
}

impl<T> Index<usize> for List<T> {
    type Output = T;

    /// Returns a reference to the value at the supplied index.
    ///
    /// # Panics
    ///
    /// Panics if the index is greater than the length of the list.
    fn index(&self, i: usize) -> &Self::Output {
        match self.nth(i) {
            Some(v) => &v,
            None => panic!("out of bounds"),
        }
    }
}

/// Creates a `List` containing the arguments.
///
/// `list!` allows `List`s to be created with the same syntax as an array.
///
/// You need to import `Cons` and `Nil` from this crate, and `std::rc::Rc` to use this macro.
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate cons_list_rs; fn main() {
/// use cons_list_rs::List::{Cons,Nil};
/// use std::rc::Rc;
/// let list = list![1, 2, 3];
/// # }
/// ```
#[macro_export]
macro_rules! list {
    () => (Nil);
    ($head:expr) => (Cons($head, Rc::new(Nil)));
    ($head:expr, $($tail:expr),*) => (Cons($head, Rc::new(list![$($tail),*])));
}

// Iterators

/// An iterator over lists with values of type `T`.
///
/// To obtain one, use `List::iter()`.
pub struct Iter<'a, T: 'a> {
    seq: &'a List<T>,
    index: usize,
}

impl<'a, T> Iter<'a, T> {
    fn new(seq: &'a List<T>) -> Self {
        Iter { seq, index: 0 }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.seq.nth(self.index);
        self.index += 1;
        value
    }
}

// IntoIterator

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_list() {
        Cons(1, Rc::new(Cons(2, Rc::new(Nil))));
    }

    #[test]
    fn simple_nth() {
        let list = Cons(1, Rc::new(Cons(2, Rc::new(Nil))));

        assert_eq!(list.nth(0), Some(&1));
        assert_eq!(list.nth(1), Some(&2));
        assert_eq!(list.nth(2), None);
        assert_eq!(list.nth(3), None);
    }

    #[test]
    fn string_list_nth() {
        let list = Cons("a", Rc::new(Cons("b", Rc::new(Nil))));

        assert_eq!(list.nth(0), Some(&"a"));
        assert_eq!(list.nth(1), Some(&"b"));
        assert_eq!(list.nth(2), None);
        assert_eq!(list.nth(3), None);
    }

    #[test]
    fn simple_sharing() {
        let a = Rc::new(Cons("a", Rc::new(Cons("b", Rc::new(Nil)))));

        let c = Cons("c", Rc::clone(&a));
        let d = Cons("d", Rc::clone(&a));

        assert_eq!(a.nth(0), Some(&"a"));
        assert_eq!(c.nth(0), Some(&"c"));
        assert_eq!(d.nth(0), Some(&"d"));
        assert_eq!(c.nth(1), Some(&"a"));
        assert_eq!(d.nth(1), Some(&"a"));
    }

    #[test]
    fn simple_index() {
        let list = Cons(1, Rc::new(Cons(2, Rc::new(Nil))));

        assert_eq!(list[0], 1);
        assert_eq!(list[1], 2);
    }

    #[test]
    #[should_panic]
    fn simple_index_panic() {
        let list = Cons(1, Rc::new(Cons(2, Rc::new(Nil))));
        list[2];
    }

    #[test]
    fn string_index() {
        let list = Rc::new(Cons("a", Rc::new(Cons("b", Rc::new(Nil)))));

        assert_eq!(list[0], "a");
        assert_eq!(list[1], "b");
    }

    #[test]
    fn simple_len() {
        let list = Cons(1, Rc::new(Cons(2, Rc::new(Nil))));

        assert_eq!(list.len(), 2)
    }

    #[test]
    fn single_item_list_macro() {
        let list = list![1];

        assert_eq!(list[0], 1);
        assert_eq!(list.len(), 1);
    }

    #[test]
    fn empty_list_macro() {
        let list: List<i32> = list![];

        assert_eq!(list.nth(0), None);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn two_item_list_macro() {
        let list = list![1, 2];

        assert_eq!(list[0], 1);
        assert_eq!(list[1], 2);
        assert_eq!(list.len(), 2);
    }

    #[test]
    fn three_item_list_macro() {
        let list = list![1, 2, 3];

        assert_eq!(list[0], 1);
        assert_eq!(list[1], 2);
        assert_eq!(list[2], 3);
        assert_eq!(list.len(), 3);
    }

    // Iterators

    #[test]
    fn iter_simple() {
        let list = list![1, 2, 3];
        let mut iter = Iter::new(&list);

        assert_eq!(Some(&1), iter.next());
        assert_eq!(Some(&2), iter.next());
        assert_eq!(Some(&3), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn list_iter() {
        let list = list![1, 2, 3];
        let mut iter = list.iter();

        assert_eq!(Some(&1), iter.next());
        assert_eq!(Some(&2), iter.next());
        assert_eq!(Some(&3), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn list_into_iter() {
        let list = list![1, 2, 3];
        let mut iter = list.into_iter();

        assert_eq!(Some(&1), iter.next());
        assert_eq!(Some(&2), iter.next());
        assert_eq!(Some(&3), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn list_for() {
        let list = list![1,2,3];
        let mut sum = 0;

        for i in list.into_iter() {
            sum += i
        }

        assert_eq!(6, sum);
    }
}
