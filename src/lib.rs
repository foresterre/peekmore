#![no_std]
#![deny(missing_docs)]

//! **Synopsis:**
//!
//! This crate introduces a multi-peekable iterator.
//! The iterator is similar to [`Peekable`]. The main difference is that [`Peekable`] only
//! allows you to peek at the next element and no further. This crate aims to take that limitation
//! away.
//!
//! **A peek at how it works:**
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
//!
//! **Illustrated example:**
//!
//! An illustrated example can be found at the [`PeekMoreIterator::peek`] documentation.
//!
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
//! // Peek at the second element (the element our cursor points at also moved to the second element,
//! // since the first element was consumed.)
//! let v2 = iter.peek();
//! assert_eq!(v2, Some(&&2));
//!
//! // Advance the cursor. The cursor will now point to the third element.
//! let _ = iter.move_next();
//!
//! // Check that it is indeed at the third element.
//! let v3 = iter.peek();
//! assert_eq!(v3, Some(&&3));
//!
//! // Reset the position the cursor points at. The cursor will point to the first unconsumed element
//! // again.
//! iter.reset_cursor();
//!
//! // Check that we are indeed at the second element again.
//! let v2 = iter.peek();
//! assert_eq!(v2, Some(&&2));
//!
//! // Shift the position of the cursor to the right twice by chaining the advance_view method.
//! let _ = iter.move_next().move_next();
//!
//! // Verify that the cursor indeed points at the fourth element.
//! let v4 = iter.peek();
//! assert_eq!(v4, Some(&&4));
//!
//! // Reset the position which the cursor points at again.
//! iter.reset_cursor();
//!
//! // We can also advance the cursor and peek with a single operation.
//! let v3 = iter.peek_next();
//! assert_eq!(v3, Some(&&3));
//! ```
//!
//!
//! [`Peekable`]: https://doc.rust-lang.org/core/iter/struct.Peekable.html
//! [`PeekMoreIterator::peek`]: struct.PeekMoreIterator.html#method.peek
//! [requires]: https://github.com/servo/rust-smallvec/issues/160

/// We do need to allocate to save and store elements which are in the future compared to our last
/// iterator element. By default a Vec is used, but SmallVec is optionally also available.
extern crate alloc;

/// Import std only when running doc tests without errors. Std will not be included outside of
/// doctest based binaries.
///
/// See [rust#54010](https://github.com/rust-lang/rust/issues/54010) for the error thrown by `doctest`
/// if no allocator is present (e.g. with just core/alloc).
/// Note that `cfg(doctest)` requires Rust 1.40 ([tracking issue](https://github.com/rust-lang/rust/issues/62210)).
/// As a result of the above, `doctest` is disabled on the CI for Rust versions below `1.40`.
#[cfg(doctest)]
extern crate std;

/// Use the system allocator when running doc tests.
///
/// See [rust#54010](https://github.com/rust-lang/rust/issues/54010) for the error thrown by `doctest`
/// if no allocator is present (e.g. with just core/alloc).
/// Note that `cfg(doctest)` requires Rust 1.40 ([tracking issue](https://github.com/rust-lang/rust/issues/62210)).
/// As a result of the above, `doctest` is disabled on the CI for Rust versions below `1.40`.
#[cfg(doctest)]
#[global_allocator]
static A: std::alloc::System = std::alloc::System;

use core::iter::FusedIterator;

/// We use a Vec to queue iterator elements if the smallvec feature is disabled.
#[cfg(not(feature = "smallvec"))]
use alloc::vec::Vec;

/// If the smallvec feature is enabled, we use a SmallVec to queue iterator elements instead of a Vec.
#[cfg(feature = "smallvec")]
use smallvec::SmallVec;

/// Trait which allows you to create an iterator which allows us to peek at any unconsumed element.
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

            cursor: 0usize,
        }
    }
}

/// Default stack size for SmallVec.
/// Admittedly the current size is chosen quite arbitrarily.
#[cfg(feature = "smallvec")]
const DEFAULT_STACK_SIZE: usize = 256;

/// This iterator makes it possible to peek multiple times without consuming a value.
/// In reality the underlying iterator will be consumed, but the values will be stored in a local
/// queue. This queue allows us to move around unconsumed elements (as far as the iterator is concerned).
#[derive(Clone, Debug)]
pub struct PeekMoreIterator<I: Iterator> {
    /// Inner iterator. Consumption of this inner iterator does not represent consumption of the
    /// PeekMoreIterator.
    iterator: I,

    /// The queue represent the items of our iterator which have not been consumed, but have been
    /// prepared to view ('peek' at) without consuming them. Once an element has been consumed by
    /// the iterator, it is no longer possible to peek at it either (and will be removed from the
    /// queue).
    #[cfg(not(feature = "smallvec"))]
    queue: Vec<Option<I::Item>>,
    #[cfg(feature = "smallvec")]
    queue: SmallVec<[Option<I::Item>; DEFAULT_STACK_SIZE]>,

    /// The cursor helps us determine which item we currently have in view.
    ///
    /// If the cursor is 0, we have not advanced (or have reset) our peeking window, and
    /// it will point to the equivalent element as what [`core::iter::Peekable::peek`] would point to.  
    ///
    /// [`core::iter::Peekable::peek`]: https://doc.rust-lang.org/core/iter/struct.Peekable.html#method.peek
    cursor: usize,
}

impl<I: Iterator> PeekMoreIterator<I> {
    /// Get a reference to the element where the cursor currently points at (if such element exists).
    /// Sometimes we also call this the current 'view'.
    ///
    /// If we haven't advanced our cursor, that will be the same element as the one `next()` would
    /// return, but if we have moved our cursor, it will be the element we moved to instead.
    /// Note that the cursor can't ever point at an element (which existed) before the first
    /// unconsumed element within the iterator. In a sense the cursor moves independently within the
    /// iterator. But it will always stick to unconsumed elements.
    ///
    /// The following illustration aims to show how `peek()` behaves. `i` represents the position
    /// of the iterator (i.e. the next value that will be returned if `next()` is called) and `j`
    /// represents the position of the cursor (i.e. the current element referenced if
    /// `peek()` is called).
    /// In example code next to the illustrations, the first element `1` is analogous to `A`,
    /// `2` to `B` etc.
    ///
    /// * start:
    ///
    /// ```rust
    /// use peekmore::PeekMore;
    ///
    /// // Initialize our iterator.
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
    /// let iter = iterator.move_next();
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
    /// (The reference returned by `peek()` will not change, similar to the behaviour of
    /// [`core::iter::Peekable::peek`].
    ///      In order to move to the next peekable element, we need to advance our view.)
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.move_next();
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&2));
    ///
    /// // Calling peek() multiple times doesn't shift the position of our cursor;
    /// // a reference to the same element will be returned each call.
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
    ///     (i.e. advance the iterator; the element represented by A will be consumed)
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.move_next();
    /// let i = iterator.next();
    /// assert_eq!(i, Some(&1));
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A |     | B |  --> | C | --> | D | --> None --> None --> ...
    /// -----     -----      -----     -----
    ///             ^
    ///             i, j
    ///  returns Some(A)
    /// ```
    ///
    /// * call `next()`.
    ///     (i.e. advance the iterator again; we'll see that the cursor position shifts to the
    ///      next iterator position if the iterator consumes elements where our cursor pointed at
    ///      previously (that is if `j < i`))
    ///
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.move_next();
    /// # let _ = iterator.next();
    /// // Show that the cursor still points at the second element.
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&2));
    ///
    /// // Consume the second element.
    /// let i = iterator.next();
    /// assert_eq!(i, Some(&2));
    ///
    /// // Our cursor previously pointed at the element represented by B. Since that element has
    /// // been consumed, the cursor shifts to the next unconsumed element: C.
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&3));
    ///
    ///
    /// ```
    ///
    /// ```txt
    /// -----     -----      -----     -----
    /// | A |     | B |      | C | --> | D | --> None --> None --> ...
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
    /// # let iter = iterator.move_next();
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
        self.fill_queue(self.cursor);
        self.queue.get(self.cursor).and_then(|v| v.as_ref())
    }

    // Convenient as we don't have to re-assign our mutable borrow on the 'user' side.
    /// Advance the cursor to the next element and return a reference to that value.
    #[inline]
    pub fn peek_next(&mut self) -> Option<&I::Item> {
        let this = self.move_next();
        this.peek()
    }

    /// Try to peek at a previous element. If no such element exists (i.e. our cursor is already
    /// at the same point as the next iterator element), it will return an `Err` result containing a
    /// [`PeekMoreError::ElementHasBeenConsumed`].
    /// If a previous element does exist, an option wrapped in an `Ok` result will be returned.
    ///
    ///  `Result` is re
    ///
    /// [`PeekMoreError::ElementHasBeenConsumed`]: enum.PeekMoreError.html#variant.ElementHasBeenConsumed
    #[inline]
    pub fn peek_previous(&mut self) -> Result<Option<&I::Item>, PeekMoreError> {
        if self.cursor >= 1 {
            self.decrement_needle();
            Ok(self.peek())
        } else {
            Err(PeekMoreError::ElementHasBeenConsumed)
        }
    }

    /// Move the cursor `n` steps forward and peek at the element the cursor then points to.
    #[inline]
    pub fn peek_forward(&mut self, n: usize) -> Option<&I::Item> {
        let this = self.move_forward(n);
        this.peek()
    }

    /// Move the cursor `n` steps backward and peek at the element the cursor then points to.
    ///
    /// If there aren't `n` elements prior to the element the cursor currently points at, a
    /// [`PeekMoreError::ElementHasBeenConsumed`] is returned instead.
    /// The cursor will then stay at the position it was prior to calling this method.
    ///
    /// If you want to peek at the first unconsumed element instead of returning with an error, you
    /// can use the [`peek_backward_or_first`] method instead of this one.
    ///
    /// [`PeekMoreError::ElementHasBeenConsumed`]: enum.PeekMoreError.html#variant.ElementHasBeenConsumed
    /// [`peek_backward_or_first`]: struct.PeekMoreIterator.html#method.peek_backward_or_first
    #[inline]
    pub fn peek_backward(&mut self, n: usize) -> Result<Option<&I::Item>, PeekMoreError> {
        let _ = self.move_backward(n)?;

        Ok(self.peek())
    }

    /// Move the cursor `n` steps backward and peek at the element the cursor then points to, or
    /// if there aren't `n` elements prior to the element the cursor currently points to, peek at
    /// the first unconsumed element instead.
    #[inline]
    pub fn peek_backward_or_first(&mut self, n: usize) -> Option<&I::Item> {
        if self.move_backward(n).is_err() {
            self.reset_cursor();
        }

        self.peek()
    }

    /// Peek at the nth element without moving the cursor.
    #[inline]
    pub fn peek_nth(&mut self, n: usize) -> Option<&I::Item> {
        self.fill_queue(n);
        self.queue.get(n).and_then(|v| v.as_ref())
    }

    /// Move the cursor to the next peekable element.
    /// This does not advance the iterator itself. To advance the iterator, use [`Iterator::next()`].
    ///
    /// A mutable reference to the iterator is returned.
    /// This operation can be chained.
    ///
    /// [`Iterator::next()`]: struct.PeekMoreIterator.html#impl-Iterator
    #[inline]
    pub fn move_next(&mut self) -> &mut PeekMoreIterator<I> {
        self.increment_needle();
        self
    }

    /// Move the cursor to the previous peekable element.
    /// If such element doesn't exist, returns a [`PeekMoreError::ElementHasBeenConsumed`] wrapped
    /// in the `Err` variant of `Result`.
    ///
    /// If we can move to a previous element, a mutable reference to the iterator,
    /// wrapped in the `Ok` variant of `Result` will be returned.
    ///
    /// [`PeekMoreError::ElementHasBeenConsumed`]: enum.PeekMoreError.html#variant.ElementHasBeenConsumed
    #[inline]
    pub fn move_previous(&mut self) -> Result<&mut PeekMoreIterator<I>, PeekMoreError> {
        if self.cursor >= 1 {
            self.decrement_needle();
            Ok(self)
        } else {
            Err(PeekMoreError::ElementHasBeenConsumed)
        }
    }

    /// Move the cursor `n` elements forward.
    /// This does not advance the iterator itself. To advance the iterator, use [`Iterator::next()`].
    ///
    /// [`Iterator::next()`]: struct.PeekMoreIterator.html#impl-Iterator
    #[inline]
    pub fn move_forward(&mut self, n: usize) -> &mut PeekMoreIterator<I> {
        self.cursor += n;
        self
    }

    /// Moves the cursor forward for as many elements as a predicate is true.
    #[inline]
    pub fn move_forward_while<P: Fn(Option<&I::Item>) -> bool>(
        &mut self,
        predicate: P,
    ) -> &mut PeekMoreIterator<I> {
        let view = self.peek();

        if predicate(view) {
            self.increment_needle();
            self.move_forward_while(predicate)
        } else {
            self.decrement_needle();
            self
        }
    }

    /// Move the cursor `n` elements backward. If there aren't `n` unconsumed elements prior to the
    /// cursor it will return an error. In case of an error, the cursor will stay at the position
    /// it pointed at prior to calling this method.
    ///
    /// If you want to reset the cursor to the first unconsumed element even if there aren't `n`
    /// unconsumed elements before the position the cursor points at, you can use the
    /// [`move_backward_or_reset`] method instead.
    ///
    /// [`move_backward_or_reset`]: struct.PeekMoreIterator.html#method.move_backward_or_reset
    #[inline]
    pub fn move_backward(&mut self, n: usize) -> Result<&mut PeekMoreIterator<I>, PeekMoreError> {
        if self.cursor < n {
            Err(PeekMoreError::ElementHasBeenConsumed)
        } else {
            self.cursor -= n;
            Ok(self)
        }
    }

    /// Move the cursor `n` elements backward or reset to the first non consumed element if
    /// we can't move the cursor `n` elements to the back.
    #[inline]
    pub fn move_backward_or_reset(&mut self, n: usize) -> &mut PeekMoreIterator<I> {
        if self.cursor < n {
            self.reset_cursor();
        } else {
            self.cursor -= n;
        }

        self
    }

    /// Move the cursor to the n-th element of the queue.
    #[inline]
    pub fn move_nth(&mut self, n: usize) -> &mut PeekMoreIterator<I> {
        self.cursor = n;
        self
    }

    /// Deprecated: use [`reset_cursor`] instead.
    ///
    /// [`reset_cursor`]: struct.PeekMoreIterator.html#method.reset_cursor
    #[deprecated]
    #[inline]
    pub fn reset_view(&mut self) {
        self.reset_cursor()
    }

    /// Reset the position of the cursor. If we call [`peek`] just after a reset,
    /// it will return a reference to the first element again.
    ///
    /// [`peek`]: struct.PeekMoreIterator.html#method.peek
    #[inline]
    pub fn reset_cursor(&mut self) {
        self.cursor = 0;
    }

    /// Fills the queue up to (including) the cursor.
    #[inline]
    fn fill_queue(&mut self, required_elements: usize) {
        let stored_elements = self.queue.len();

        if stored_elements <= required_elements {
            for _ in stored_elements..=required_elements {
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

    /// Increment the cursor which points to the current peekable item.
    /// Note: if the cursor is [core::usize::MAX], it will not increment any further.
    ///
    /// [core::usize::MAX]: https://doc.rust-lang.org/core/usize/constant.MAX.html
    #[inline]
    fn increment_needle(&mut self) {
        // do not overflow
        if self.cursor < core::usize::MAX {
            self.cursor += 1;
        }
    }

    /// Decrement the cursor which points to the current peekable item.
    /// Note: if the cursor is [core::usize::MIN], it will not decrement any further.
    ///
    /// [core::usize::MIN]: https://doc.rust-lang.org/core/usize/constant.MIN.html
    #[inline]
    fn decrement_needle(&mut self) {
        if self.cursor > core::usize::MIN {
            self.cursor -= 1;
        }
    }

    #[doc(hidden)]
    pub fn needle_position(&self) -> usize {
        self.cursor
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

/// This enumeration provides errors which represent lack of success of the [`PeekMoreIterator`].
///
/// [`PeekMoreIterator`]: struct.PeekMoreIterator.html
#[derive(Debug, Eq, PartialEq)]
pub enum PeekMoreError {
    /// This error case will be returned if we try to move to an element, but it has already been
    /// consumed by the iterator.
    /// We can only peek at elements which haven't been consumed.
    ElementHasBeenConsumed,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peek_forward_with_reassignment() {
        let iterable = [1, 2, 3, 4];

        let mut peek = iterable.iter().peekmore();

        assert_eq!(peek.peek(), Some(&&1));

        let peek = peek.move_next();
        assert_eq!(peek.peek(), Some(&&2));

        let peek = peek.move_next();
        assert_eq!(peek.peek(), Some(&&3));

        let peek = peek.move_next();
        assert_eq!(peek.peek(), Some(&&4));

        let peek = peek.move_next();
        assert_eq!(peek.peek(), None);
    }

    #[test]
    fn peek_forward_without_reassignment_separately_advance_and_peek() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek(), Some(&&1));

        let v2 = iter.move_next().peek();
        assert_eq!(v2, Some(&&2));

        let v3 = iter.move_next().peek();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.move_next().peek();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.move_next().peek();
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

        iter.reset_cursor();
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

        let iter = iter.move_next();
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
        iter.reset_cursor();

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

        iter.reset_cursor();

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

        iter.move_next(); // j -> 2
        assert_eq!(iter.needle_position(), 1);

        iter.move_next(); // j -> 3
        assert_eq!(iter.needle_position(), 2);

        iter.move_next(); // j -> 4
        assert_eq!(iter.needle_position(), 3);

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));
    }

    #[test]
    fn check_advance_chain() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore(); // j -> 1

        assert_eq!(iter.needle_position(), 0);

        iter.move_next() // j -> 2
            .move_next() // j -> 3
            .move_next(); // j -> 4

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));
    }

    #[test]
    fn check_move_previous() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore(); // j -> 1

        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek(), Some(&&1));

        iter.move_next(); // j -> 2
        assert_eq!(iter.needle_position(), 1);

        let _ = iter.move_previous(); // j -> 1
        assert_eq!(iter.needle_position(), 0);

        iter.move_next(); // j -> 2
        assert_eq!(iter.needle_position(), 1);

        let _ = iter.move_previous(); // j -> 1
        assert_eq!(iter.needle_position(), 0);

        iter.move_next(); // j -> 2
        assert_eq!(iter.needle_position(), 1);

        iter.move_next() // j -> 3
            .move_next(); // j -> 4

        assert_eq!(iter.needle_position(), 3);

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));

        let _ = iter.move_previous().and_then(|it| {
            it.move_previous() // j -> 3
                .and_then(|it| {
                    it.move_previous() // j -> 2
                        .and_then(|it| it.move_previous())
                })
        }); // j -> 1

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));

        let prev = iter.move_previous();
        assert!(prev.is_err());

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));
    }

    #[test]
    fn test_with_inherited_feature_count() {
        let iterable = [1, 2, 3];
        let mut iter = iterable.iter().peekmore();

        iter.move_next();
        let second = iter.peek().unwrap();
        assert_eq!(second, &&2);

        let consume_first = iter.next().unwrap();
        assert_eq!(consume_first, &1);

        let count = iter.count();
        assert_eq!(count, 2);
    }

    #[test]
    fn peek_previous() {
        let iterable = [1, 2, 3];
        let mut iter = iterable.iter().peekmore(); // j = 1

        iter.move_next(); // j = 2
        iter.move_next(); // j = 3
        let value = iter.peek().unwrap(); // 3
        assert_eq!(value, &&3);

        let peek = iter.peek_previous(); // 2
        assert_eq!(peek.unwrap(), Some(&&2));
        assert_eq!(iter.needle_position(), 1);

        let peek = iter.peek_previous(); // 1
        assert_eq!(peek.unwrap(), Some(&&1));
        assert_eq!(iter.needle_position(), 0);

        let peek = iter.peek_previous();
        assert_eq!(peek, Err(PeekMoreError::ElementHasBeenConsumed));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn peek_previous_beyond_none() {
        let iterable = [1];
        let mut iter = iterable.iter().peekmore(); // j = 1
        assert_eq!(iter.needle_position(), 0);

        iter.move_next(); // j = None (1)
        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 1);

        iter.move_next(); // j = None (2)
        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 2);

        iter.move_next(); // j = None (3)
        let peek = iter.peek(); // current
        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 3);

        let peek = iter.peek_previous(); // None (2)
        assert_eq!(peek.unwrap(), None);
        assert_eq!(iter.needle_position(), 2);

        let peek = iter.peek_previous(); // None (1)
        assert_eq!(peek.unwrap(), None);
        assert_eq!(iter.needle_position(), 1);

        let peek = iter.peek_previous(); // 1
        assert_eq!(peek.unwrap(), Some(&&1));
        assert_eq!(iter.needle_position(), 0);

        let peek = iter.peek_previous();
        assert_eq!(peek, Err(PeekMoreError::ElementHasBeenConsumed));
        assert_eq!(iter.needle_position(), 0);

        let peek = iter.peek_previous();
        assert_eq!(peek, Err(PeekMoreError::ElementHasBeenConsumed));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_forward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let _ = iter.move_forward(3);
        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 6);
    }

    #[test]
    fn check_move_backward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let result = iter.move_backward(2);
        assert!(result.is_ok());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&2));
        assert_eq!(iter.needle_position(), 1);

        let result = iter.move_backward(1);
        assert!(result.is_ok());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);

        let result = iter.move_backward(1);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_backward_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let result = iter.move_backward(5);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);
    }

    #[test]
    fn check_move_backward_or_reset() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let _ = iter.move_backward_or_reset(2);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&2));
        assert_eq!(iter.needle_position(), 1);

        let _ = iter.move_backward_or_reset(1);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);

        let _ = iter.move_backward_or_reset(1);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_backward_or_reset_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let _ = iter.move_backward_or_reset(5);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_backward_or_reset_empty() {
        let iterable = "".chars();

        let mut iter = iterable.peekmore();

        assert_eq!(iter.peek(), None);
        assert_eq!(iter.needle_position(), 0);

        let _ = iter.move_backward_or_reset(5);

        assert_eq!(iter.peek(), None);
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_peek_forward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let peek = iter.peek_forward(3);

        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let peek = iter.peek_forward(3);
        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 6);
    }

    #[test]
    fn check_peek_backward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let result = iter.peek_backward(2);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Some(&&2));
        assert_eq!(iter.needle_position(), 1);

        let result = iter.peek_backward(1);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Some(&&1));
        assert_eq!(iter.needle_position(), 0);

        let result = iter.peek_backward(1);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_peek_backward_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let result = iter.peek_backward(5);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);
    }

    #[test]
    fn check_peek_backward_or_first_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);

        let peek = iter.peek_backward_or_first(5);
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_peek_backward_or_first_empty() {
        let iterable = "".chars();

        let mut iter = iterable.peekmore();

        assert_eq!(iter.peek(), None);
        assert_eq!(iter.needle_position(), 0);

        let peek = iter.peek_backward_or_first(5);

        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_forward_while() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward_while(|i| **i.unwrap() != 3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&2));
        assert_eq!(iter.needle_position(), 1);
    }

    #[test]
    fn check_move_forward_while_empty() {
        let iterable: [i32; 0] = [];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward_while(|i| if let Some(i) = i { **i != 3 } else { false });

        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_forward_while_some() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.move_forward_while(|i| i.is_some());

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.needle_position(), 3);
    }

    #[test]
    fn check_peek_nth() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek_nth(0), Some(&&1));
        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek_nth(1), Some(&&2));
        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek_nth(2), Some(&&3));
        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek_nth(3), Some(&&4));
        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek_nth(4), None);
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_peek_nth_empty() {
        let iterable: [i32; 0] = [];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek_nth(0), None);
        assert_eq!(iter.needle_position(), 0);
        assert_eq!(iter.peek_nth(1), None);
        assert_eq!(iter.needle_position(), 0);
    }

    #[test]
    fn check_move_nth() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        iter.move_nth(20);
        assert_eq!(iter.peek_nth(0), Some(&&1));
        assert_eq!(iter.needle_position(), 20);
        assert_eq!(iter.peek(), None);

        iter.move_nth(0);
        assert_eq!(iter.peek(), Some(&&1));

        iter.move_nth(3);
        assert_eq!(iter.peek(), Some(&&4));
    }

    #[test]
    fn check_move_nth_empty() {
        let iterable: [i32; 0] = [];

        let mut iter = iterable.iter().peekmore();

        iter.move_nth(0);
        assert_eq!(iter.needle_position(), 0);

        iter.move_nth(10);
        assert_eq!(iter.needle_position(), 10);
    }
}
