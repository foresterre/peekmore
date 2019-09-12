#![no_std]
#![deny(missing_docs)]

//! **Synopsis:**
//!
//! This crate introduces a multi-peekable iterator.
//! The iterator is similar to [`Peekable`]. The main difference is that [`Peekable`] only
//! allows you to peek at the next element and no further. This crate aims to take that limitation
//! away.
//!
//! **Peekable queue:**
//!
//! To enable peeking at multiple elements ahead of consuming a next element, the iterator uses a
//! traversable queue which holds the elements which you can peek at, but have not been
//! consumed (yet).
//! By default the underlying data structure of this queue is a Vec. By enabling the `smallvec`
//! feature, you can opt-in to use SmallVec as the underlying queue data structure. SmallVec uses
//! the stack for a limited amount of elements and will only allocate on the heap if this maximum
//! amount of elements is reached. SmallVec support for `no_std` is experimental and currently
//! [requires] a nightly compiler.
//!
//! **Usage example:**
//!
//! ```rust
//! use peekmore::PeekMore;
//!
//! let iterable = [1, 2, 3, 4];
//! let mut iter = iterable.iter().peekmore();
//!
//! // Peek at the first element.
//! let v1 = iter.peek();
//! assert_eq!(v1, Some(&&1));
//!
//! // Consume the first element.
//! let v1c = iter.next();
//! assert_eq!(v1c, Some(&1));
//!
//! // Peek at the second element (the element in our peek view also moved to the second element,
//! // since the first element was consumed.)
//! let v2 = iter.peek();
//! assert_eq!(v2, Some(&&2));
//!
//! // Advance the peek view. The peek view will now be at the third element.
//! let _ = iter.advance_view();
//!
//! // Check that it is indeed at the third element.
//! let v3 = iter.peek();
//! assert_eq!(v3, Some(&&3));
//!
//! // Reset our peek view to the second element (since the first element has been consumed).
//! // It is the first non-consumed element.
//! iter.reset_view();
//!
//! // Check that we are indeed at the second element again.
//! let v2 = iter.peek();
//! assert_eq!(v2, Some(&&2));
//!
//! // Shift the peek view to the right twice by chaining the advance_view method.
//! let _ = iter.advance_view().advance_view();
//!
//! // Verify that the peek view is indeed at the fourth element.
//! let v4 = iter.peek();
//! assert_eq!(v4, Some(&&4));
//!
//! // Reset the view again (.
//! iter.reset_view();
//!
//! // We can also shift the peek view and peek with a single operation.
//! let v3 = iter.peek_next();
//! assert_eq!(v3, Some(&&3));
//! ```
//!
//! **Illustrated example:**
//!
//! An illustrated example can be found at the [`PeekMoreIterator::peek`] documentation.
//!
//! [`Peekable`]: https://doc.rust-lang.org/core/iter/struct.Peekable.html
//! [`PeekMoreIterator::peek`]: struct.PeekMoreIterator.html#method.peek
//! [requires]: https://github.com/servo/rust-smallvec/issues/160

/// We do need to allocate to save and store elements which are in the future compared to our last
/// iterator element. Perhaps in the future we could optimize this slightly by using the stack for
/// a limited amount of elements.
extern crate alloc;

use core::iter::FusedIterator;

/// We use a Vec to queue iterator elements if the smallvec feature is disabled.
#[cfg(not(feature = "smallvec"))]
use alloc::vec::Vec;

/// If the smallvec feature is enabled, we use a SmallVec to queue iterator elements instead of a Vec.
#[cfg(feature = "smallvec")]
use smallvec::SmallVec;

/// Trait which allows one to create an iterator which allows us to peek multiple times forward.
pub trait PeekMore: Iterator + Sized {
    /// Create an iterator where we can look (peek) forward multiple times from an existing iterator.
    fn peekmore(self) -> PeekMoreIterator<Self>;
}

impl<I: Iterator> PeekMore for I {
    fn peekmore(self) -> PeekMoreIterator<I> {
        PeekMoreIterator {
            iterator: self,

            #[cfg(not(feature = "smallvec"))]
            queue: Vec::new(),

            #[cfg(feature = "smallvec")]
            queue: SmallVec::new(),

            needle: 0usize,
        }
    }
}

/// Default stack size for SmallVec.
/// Admittedly the current size is chosen quite arbitrarily.
#[cfg(feature = "smallvec")]
const DEFAULT_STACK_SIZE: usize = 256;

/// This iterator makes it possible to peek multiple times without consuming a value.
/// In reality the underlying iterator will be consumed, but the values will be stored in a local
/// vector. This vector allows us to shift to visible element (the 'view').
#[derive(Clone, Debug)]
pub struct PeekMoreIterator<I: Iterator> {
    /// Inner iterator. Consumption of this inner iterator does not represent consumption of the
    /// PeekMoreIterator.
    iterator: I,

    /// The queue represent the items of our iterator which have not been consumed, but have been
    /// prepared to view ('peek') without consuming them. Once an element is consumed, we can no longer
    /// view an item in the queue.
    #[cfg(not(feature = "smallvec"))]
    queue: Vec<Option<I::Item>>,
    #[cfg(feature = "smallvec")]
    queue: SmallVec<[Option<I::Item>; DEFAULT_STACK_SIZE]>,

    /// The needle helps us determine which item we currently have in view.
    /// Within these docs, it is also sometimes known as the peek view, peek view handle and peek view
    /// window.
    /// If the needle is 0, we have not advanced (or have reset) our peeking window, and
    /// it will point to the equivalent element as what [`core::iter::Peekable::peek`] would point to.  
    ///
    /// [`core::iter::Peekable::peek`]: https://doc.rust-lang.org/core/iter/struct.Peekable.html#method.peek
    needle: usize,
}

impl<I: Iterator> PeekMoreIterator<I> {
    /// Get the reference of our current peek view window.
    /// Note that `peek()` will always return a reference to the element where our current peek view
    /// handle points to.
    /// If we haven't advanced our peek view window, that will be the same element as the one next()
    /// returns, but if we have advanced our peek view, it will be the element we advanced to instead.
    ///
    /// The following illustration aims to show how `peek()` behaves. `i` represents the position
    /// of the iterator (i.e. the next value that will be returned if `next()` is called) and `j`
    /// represents the position of the current peek view (i.e. the current element referenced if
    /// `peek()` is called).
    /// In example code next to the illustrations, the first element `1` is analogous to `A`,
    /// `2` to `B` etc.
    ///
    /// * start:
    ///
    /// ```rust
    /// use peekmore::PeekMore;
    ///
    /// // initialize our iterator
    /// let iterable = [1, 2, 3, 4];
    /// let mut iterator = iterable.iter().peekmore();
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A | --> | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///   ^
    ///   i, j
    /// ```
    ///
    /// * call `peek()`:
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&1));
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A | --> | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///   ^
    ///   i, j
    ///      returns Some(&A)
    ///
    /// ```
    ///
    /// * call `advance_view()`
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// let iter = iterator.advance_view();
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A | --> | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///   ^         ^
    ///   i         j
    /// ```
    ///
    /// * call `peek()`
    ///   _or_ `peek(); peek()`  _or_ `peek(); peek(); peek()` etc.
    ///
    /// (The reference returned by `peek()` will not change, similar to the behaviour of [`core::iter::Peekable::peek`]
    ///      In order to move to the next peekable element, we need to advance our view.)
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.advance_view();
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&2));
    ///
    /// // calling peek() multiple times doesn't shift our peek view; a reference to the same element will be returned each call.
    /// assert_eq!(iterator.peek(), Some(&&2));
    /// assert_eq!(iterator.peek(), Some(&&2));
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A | --> | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///   ^         ^
    ///   i         j
    ///             returns Some(&B)
    /// ```
    ///
    ///
    /// * call `next()`
    ///     (i.e. advance the iterator; the first element will be consumed)
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.advance_view();
    /// let i = iterator.next();
    /// assert_eq!(i, Some(&1));
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A | --> | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///             ^
    ///             i, j
    ///  returns Some(A)
    /// ```
    ///
    /// * call `next()`.
    ///     (i.e. advance the iterator again; we'll see that the current peek view shifts with the
    ///      next iterator position if the iterator consumes elements where our peek view pointed at
    ///      previously (`j < i`))
    ///
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.advance_view();
    /// # let _ = iterator.next();
    /// // show that the peek view still is at element 2.
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&2));
    ///
    /// // consume the second element
    /// let i = iterator.next();
    /// assert_eq!(i, Some(&2));
    ///
    /// // while our peek view was at positioned at the second element. it is now at the third,
    /// // since the iterator consumed the second.
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&3));
    ///
    ///
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A | --> | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///                        ^
    ///                        i, j
    ///           returns Some(B)
    /// ```
    ///
    /// * Consume more elements by calling `next()` until we reach `None`:
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.advance_view();
    /// # let _ = iterator.next();
    /// # let j = iterator.peek();
    /// # assert_eq!(j, Some(&&2));
    /// # let i = iterator.next();
    /// # assert_eq!(i, Some(&2));
    /// # let j = iterator.peek();
    /// # assert_eq!(j, Some(&&3));
    /// let i = iterator.next();
    /// assert_eq!(i, Some(&3));
    ///
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&4));
    ///
    /// let i = iterator.next();
    /// assert_eq!(i, Some(&4));
    ///
    /// let j = iterator.peek();
    /// assert_eq!(j, None);
    ///
    /// let i = iterator.next();
    /// assert_eq!(i, None);
    /// ```
    /// [`core::iter::Peekable::peek`]: https://doc.rust-lang.org/core/iter/struct.Peekable.html#method.peek
    #[inline]
    pub fn peek(&mut self) -> Option<&I::Item> {
        self.fill_queue();
        self.queue.get(self.needle).and_then(|v| v.as_ref())
    }

    // convenient as we don't have to re-assign our mutable borrow on the 'user' side.
    /// Advance the view to the next element and return a reference to its value.
    #[inline]
    pub fn peek_next(&mut self) -> Option<&I::Item> {
        let this = self.advance_view();
        this.peek()
    }

    /// Advance the peekable view.
    /// This does not advance the iterator itself. To advance the iterator, use [`Iterator::next()`].
    ///
    /// [`Iterator::next()`]: struct.PeekMoreIterator.html#impl-Iterator
    #[inline]
    pub fn advance_view(&mut self) -> &mut PeekMoreIterator<I> {
        self.increment_needle();
        self
    }

    /// Reset the view. If we call [`peek`] just after a reset,
    /// it will return a reference to the first element again.
    ///
    /// [`peek`]: struct.PeekMoreIterator.html#method.peek
    #[inline]
    pub fn reset_view(&mut self) {
        self.needle = 0;
    }

    /// Fills the queue up to the needle.
    #[inline]
    fn fill_queue(&mut self) {
        if self.queue.len() <= self.needle {
            for _ in self.queue.len()..=self.needle {
                self.push_next_to_queue()
            }
        }
    }

    /// Consume the underlying iterator and push an element to the queue.
    #[inline]
    fn push_next_to_queue(&mut self) {
        let item = self.iterator.next();
        self.queue.push(item);
    }

    /// Increment the needle which points to the current peekable item.
    /// Note: if the needle is [core::usize::MAX], it will not increment any further.
    #[inline]
    fn increment_needle(&mut self) {
        // do not overflow
        if self.needle < core::usize::MAX {
            self.needle += 1;
        }
    }

    /// Decrement the needle which points to the current peekable item.
    /// Note: if the needle is [core::usize::MIN], it will not decrement any further.
    #[inline]
    fn decrement_needle(&mut self) {
        if self.needle > core::usize::MIN {
            self.needle -= 1;
        }
    }

    #[doc(hidden)]
    pub fn needle_position(&self) -> usize {
        self.needle
    }
}

impl<'a, I: Iterator> Iterator for PeekMoreIterator<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let res = if self.queue.is_empty() {
            self.iterator.next()
        } else {
            self.queue.remove(0)
        };

        self.decrement_needle();

        res
    }
}

/// Uses [`ExactSizeIterator`] default implementation.
///
/// [`ExactSizeIterator`]: https://doc.rust-lang.org/core/iter/trait.ExactSizeIterator.html
impl<I: ExactSizeIterator> ExactSizeIterator for PeekMoreIterator<I> {}

/// Uses [`FusedIterator`] default implementation.
///
/// [`FusedIterator`]: https://doc.rust-lang.org/core/iter/trait.FusedIterator.html
impl<I: FusedIterator> FusedIterator for PeekMoreIterator<I> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peek_forward_with_reassignment() {
        let iterable = [1, 2, 3, 4];

        let mut peek = iterable.iter().peekmore();

        assert_eq!(peek.peek(), Some(&&1));

        let peek = peek.advance_view();
        assert_eq!(peek.peek(), Some(&&2));

        let peek = peek.advance_view();
        assert_eq!(peek.peek(), Some(&&3));

        let peek = peek.advance_view();
        assert_eq!(peek.peek(), Some(&&4));

        let peek = peek.advance_view();
        assert_eq!(peek.peek(), None);
    }

    #[test]
    fn peek_forward_without_reassignment_separately_advance_and_peek() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek(), Some(&&1));

        let v2 = iter.advance_view().peek();
        assert_eq!(v2, Some(&&2));

        let v3 = iter.advance_view().peek();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.advance_view().peek();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.advance_view().peek();
        assert_eq!(v5, None);
    }

    #[test]
    fn peek_forward_without_reassignment_advance_and_peek_combined() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));

        let v2 = iter.peek_next();
        assert_eq!(v2, Some(&&2));

        let v3 = iter.peek_next();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.peek_next();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.peek_next();
        assert_eq!(v5, None);
    }

    #[test]
    fn peek_forward_without_reassignment_advance_and_peek_combined_and_reset_view() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));

        let v2 = iter.peek_next();
        assert_eq!(v2, Some(&&2));

        let _ = iter.reset_view();
        let v1again = iter.peek();
        assert_eq!(v1again, Some(&&1));

        let v2again = iter.peek_next();
        assert_eq!(v2again, Some(&&2));

        let v3 = iter.peek_next();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.peek_next();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.peek_next();
        assert_eq!(v5, None);
    }

    #[test]
    fn empty() {
        let iterable: [i32; 0] = [];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek(), None);

        let none = iter.peek_next();
        assert_eq!(none, None);

        let iter = iter.advance_view();
        assert_eq!(iter.peek(), None);
        assert_eq!(iter.peek_next(), None);
    }

    #[test]
    fn test_with_consume() {
        let iterable = "123".chars();

        let mut iter = iterable.peekmore();
        assert_eq!(iter.peek(), Some(&core::char::from_digit(1, 10).unwrap()));
        assert_eq!(
            iter.peek_next(),
            Some(&core::char::from_digit(2, 10).unwrap())
        );
        assert_eq!(
            iter.peek_next(),
            Some(&core::char::from_digit(3, 10).unwrap())
        );
        assert_eq!(iter.peek_next(), None);
        assert_eq!(iter.next(), Some(core::char::from_digit(1, 10).unwrap()));
        assert_eq!(iter.peek(), None);
        assert_eq!(iter.peek_next(), None);
        assert_eq!(iter.next(), Some(core::char::from_digit(2, 10).unwrap()));
        assert_eq!(iter.peek(), None);
        assert_eq!(iter.peek_next(), None);
        assert_eq!(iter.next(), Some(core::char::from_digit(3, 10).unwrap()));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.peek_next(), None);
    }

    #[test]
    fn test_with_consume_and_reset() {
        let iterable = "456".chars();

        let mut iter = iterable.peekmore();
        assert_eq!(iter.peek(), Some(&core::char::from_digit(4, 10).unwrap()));
        assert_eq!(
            iter.peek_next(),
            Some(&core::char::from_digit(5, 10).unwrap())
        );
        assert_eq!(
            iter.peek_next(),
            Some(&core::char::from_digit(6, 10).unwrap())
        );
        assert_eq!(iter.peek_next(), None);
        assert_eq!(iter.next(), Some(core::char::from_digit(4, 10).unwrap()));
        iter.reset_view();

        assert_eq!(iter.peek(), Some(&core::char::from_digit(5, 10).unwrap()));
        assert_eq!(
            iter.peek_next(),
            Some(&core::char::from_digit(6, 10).unwrap())
        );

        assert_eq!(iter.next(), Some(core::char::from_digit(5, 10).unwrap()));
        assert_eq!(iter.next(), Some(core::char::from_digit(6, 10).unwrap()));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.peek_next(), None);
    }

    #[test]
    fn check_peek_window_moves_with_consume() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));

        let v1c = iter.next();
        assert_eq!(v1c, Some(&1));

        let v2 = iter.peek();
        assert_eq!(v2, Some(&&2));

        let v2c = iter.next();
        assert_eq!(v2c, Some(&2));

        let v3 = iter.peek();
        assert_eq!(v3, Some(&&3));

        iter.reset_view();

        let v3 = iter.peek();
        assert_eq!(v3, Some(&&3));

        let v3c = iter.next();
        assert_eq!(v3c, Some(&3));

        let v4c = iter.next();
        assert_eq!(v4c, Some(&4));

        let v5 = iter.peek();
        assert_eq!(v5, None);

        let v5c = iter.next();
        assert_eq!(v5c, None);
    }

    #[test]
    fn check_advance_separately() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore(); // j -> 1

        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek(), Some(&&1));

        iter.advance_view(); // j -> 2
        assert_eq!(iter.needle_position(), 1);

        iter.advance_view(); // j -> 3
        assert_eq!(iter.needle_position(), 2);

        iter.advance_view(); // j -> 4
        assert_eq!(iter.needle_position(), 3);

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));
    }

    #[test]
    fn check_advance_chain() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore(); // j -> 1

        assert_eq!(iter.needle_position(), 0);

        iter.advance_view() // j -> 2
            .advance_view() // j -> 3
            .advance_view(); // j -> 4

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));
    }

    #[test]
    fn test_with_inherited_feature_count() {
        let iterable = [1, 2, 3];
        let mut iter = iterable.iter().peekmore();

        iter.advance_view();
        let second = iter.peek().unwrap();
        assert_eq!(second, &&2);

        let consume_first = iter.next().unwrap();
        assert_eq!(consume_first, &1);

        let count = iter.count();
        assert_eq!(count, 2);
    }
}
