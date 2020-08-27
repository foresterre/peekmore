#![no_std]
#![deny(missing_docs)]
#![deny(clippy::all)]

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
//! amount of elements is reached.
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
//! let _ = iter.advance_cursor();
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
//! let _ = iter.advance_cursor().advance_cursor();
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

/// We need to allocate elements which haven't been consumed by the PeekMore iterator.
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
    /// * call `advance_cursor()`
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// let iter = iterator.advance_cursor();
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
    /// # let iter = iterator.advance_cursor();
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
    /// # let iter = iterator.advance_cursor();
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
    /// # let iter = iterator.advance_cursor();
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
    /// # let iter = iterator.advance_cursor();
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
        let this = self.advance_cursor();
        this.peek()
    }

    /// Try to peek at a previous element. If no such element exists (i.e. our cursor is already
    /// at the same point as the next iterator element), it will return an `Err` result containing a
    /// [`PeekMoreError::ElementHasBeenConsumed`].
    /// If a previous element does exist, an option wrapped in an `Ok` result will be returned.
    ///
    /// [`PeekMoreError::ElementHasBeenConsumed`]: enum.PeekMoreError.html#variant.ElementHasBeenConsumed
    #[inline]
    pub fn peek_previous(&mut self) -> Result<Option<&I::Item>, PeekMoreError> {
        if self.cursor >= 1 {
            self.move_cursor_back().map(|iter| iter.peek())
        } else {
            Err(PeekMoreError::ElementHasBeenConsumed)
        }
    }

    /// Move the cursor `n` steps forward and peek at the element the cursor then points to.
    #[inline]
    pub fn peek_forward(&mut self, n: usize) -> Option<&I::Item> {
        let this = self.advance_cursor_by(n);
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
        let _ = self.move_cursor_back_by(n)?;

        Ok(self.peek())
    }

    /// Move the cursor `n` steps backward and peek at the element the cursor then points to, or
    /// if there aren't `n` elements prior to the element the cursor currently points to, peek at
    /// the first unconsumed element instead.
    #[inline]
    pub fn peek_backward_or_first(&mut self, n: usize) -> Option<&I::Item> {
        if self.move_cursor_back_by(n).is_err() {
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
    pub fn advance_cursor(&mut self) -> &mut PeekMoreIterator<I> {
        self.increment_cursor();
        self
    }

    /// Move the cursor `n` elements forward.
    /// This does not advance the iterator itself. To advance the iterator, use [`Iterator::next()`].
    ///
    /// [`Iterator::next()`]: struct.PeekMoreIterator.html#impl-Iterator
    #[inline]
    pub fn advance_cursor_by(&mut self, n: usize) -> &mut PeekMoreIterator<I> {
        self.cursor += n;
        self
    }

    /// Moves the cursor forward for as many elements as a predicate is true.
    #[inline]
    pub fn advance_cursor_while<P: Fn(Option<&I::Item>) -> bool>(
        &mut self,
        predicate: P,
    ) -> &mut PeekMoreIterator<I> {
        let view = self.peek();

        if predicate(view) {
            self.increment_cursor();
            self.advance_cursor_while(predicate)
        } else {
            self.decrement_cursor();
            self
        }
    }

    /// Move the cursor to the previous peekable element.
    /// If such an element doesn't exist, returns a [`PeekMoreError::ElementHasBeenConsumed`].
    ///
    /// If we can move to a previous element, a mutable reference to the iterator,
    /// wrapped in the `Ok` variant of `Result` will be returned.
    ///
    /// [`PeekMoreError::ElementHasBeenConsumed`]: enum.PeekMoreError.html#variant.ElementHasBeenConsumed
    #[inline]
    pub fn move_cursor_back(&mut self) -> Result<&mut PeekMoreIterator<I>, PeekMoreError> {
        if self.cursor >= 1 {
            self.decrement_cursor();
            Ok(self)
        } else {
            Err(PeekMoreError::ElementHasBeenConsumed)
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
    pub fn move_cursor_back_by(
        &mut self,
        n: usize,
    ) -> Result<&mut PeekMoreIterator<I>, PeekMoreError> {
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
    pub fn move_cursor_back_or_reset(&mut self, n: usize) -> &mut PeekMoreIterator<I> {
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
    fn increment_cursor(&mut self) {
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
    fn decrement_cursor(&mut self) {
        if self.cursor > core::usize::MIN {
            self.cursor -= 1;
        }
    }

    #[doc(hidden)]
    #[cfg(test)]
    fn cursor(&self) -> usize {
        self.cursor
    }

    /// Remove all elements from the start of the iterator until reaching the same
    /// position as the cursor by calling `Iterator::next()`
    ///
    /// After calling this method, `iter.peek() == iter.next().as_ref()`
    ///```rust
    /// use peekmore::PeekMore;
    ///
    /// let iterable = [1, 2, 3, 4];
    /// let mut iter = iterable.iter().peekmore();
    ///
    /// iter.advance_cursor_by(2);
    /// assert_eq!(iter.peek(), Some(&&3));
    /// assert_eq!(iter.next(), Some(&1));
    /// iter.truncate_iterator_to_cursor();
    /// assert_eq!(iter.peek(), Some(&&3));
    /// assert_eq!(iter.next(), Some(&3));
    ///```
    pub fn truncate_iterator_to_cursor(&mut self) {
        // if the cursor and the queue length are equal,
        // then we want to clear the queue completely
        let is_equal = self.cursor == self.queue.len();

        // if the cursor is greater than the queue length,
        // we want to remove the overflow from the iterator
        for _ in 0..self.cursor.saturating_sub(self.queue.len()) {
            let _ = self.iterator.next();
        }

        self.cursor = 0;

        // if `self.queue.pop()` is `None`, then it is not necessary
        // to clear the queue
        //
        // otherwise, we pop the last item and clear the queue.
        // if the cursor and queue were equal, then we discard the value
        //
        // otherwise we insert it back into the queue
        if let Some(v) = self.queue.pop() {
            self.queue.clear();
            if !is_equal {
                self.queue.push(v);
            }
        }
    }

    /// Returns a view for the next `start` (inclusive) to `end` (exclusive) elements.
    /// Note that `start` and `end`  represent indices and start at `0`.
    /// These indices always starts at the beginning of the queue  (the unconsumed
    /// iterator) for this method and don't take the position of the cursor into account.
    ///
    /// **panics** if `start > end`, in which case the range would be negative
    ///
    /// ```
    /// use peekmore::PeekMore;
    ///
    /// let iterable = [1, 2, 3, 4];
    /// let mut iter = iterable.iter().peekmore();
    ///
    /// match iter.peek_range(1, 3) {
    ///     [Some(2), Some(p)] => println!("Yay! we found number {} after number 2", p),
    ///     _ => println!("Oh noes!"),
    /// }
    /// ```
    // implementation choice:
    // why not core::ops::RangeBound<T>? it adds unnecessary complexity since we would need to define what
    // unbounded bounds mean (e.g. for end whether it would be the end of the queue or the unconsumed iterator
    // elements until None or that it won't be allowed, or some other definition), we would need to map
    // the range Inclusive and Exclusive and Unbound-ed elements to usize, and we would need to verify
    // that T would be an unsigned integer. Using RangeBound would not be all negative though since we
    // could then use the standard Rust range syntax options such as 0..4 or 0..=3, which clearly
    // tell a user what kind of bounds are used (inclusive, exclusive, etc.)
    // For now however, for the reason of not adding unnecessary complexity, I've decided
    // that the simplicity of concrete start and end types is the better choice.
    pub fn peek_range(&mut self, start: usize, end: usize) -> &[Option<I::Item>] {
        assert!(
            start <= end,
            "range of the peeked view [start, end] should be positive (i.e. start <= end)"
        );

        // fill the queue if we don't have enough elements
        if end > self.queue.len() {
            self.fill_queue(end);
        }

        // return a view of the selected range

        &self.queue.as_slice()[start..end]
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

        self.decrement_cursor();

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
    fn readme_example() {
        let range10 = 0..11;
        let mut peekable = range10.peekmore();

        // Peek at the first element
        let peek_first = peekable.peek();
        assert_eq!(*peek_first.unwrap(), 0);

        let peek_first_redux = peekable.peek_nth(0);
        assert_eq!(*peek_first_redux.unwrap(), 0);

        // Peek at the 10th (index) element
        let peek_tenth = peekable.peek_nth(10);
        assert_eq!(*peek_tenth.unwrap(), 10);

        // Consume the 10th element
        let tenth = peekable.nth(10);
        assert_eq!(tenth.unwrap(), 10);

        // Show that there are no more elements
        assert_eq!(peekable.peek(), None);
        assert_eq!(peekable.next(), None);
    }

    #[test]
    fn peek_forward_with_reassignment() {
        let iterable = [1, 2, 3, 4];

        let mut peek = iterable.iter().peekmore();

        assert_eq!(peek.peek(), Some(&&1));

        let peek = peek.advance_cursor();
        assert_eq!(peek.peek(), Some(&&2));

        let peek = peek.advance_cursor();
        assert_eq!(peek.peek(), Some(&&3));

        let peek = peek.advance_cursor();
        assert_eq!(peek.peek(), Some(&&4));

        let peek = peek.advance_cursor();
        assert_eq!(peek.peek(), None);
    }

    #[test]
    fn peek_forward_without_reassignment_separately_advance_and_peek() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek(), Some(&&1));

        let v2 = iter.advance_cursor().peek();
        assert_eq!(v2, Some(&&2));

        let v3 = iter.advance_cursor().peek();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.advance_cursor().peek();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.advance_cursor().peek();
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

        let iter = iter.advance_cursor();
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

        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek(), Some(&&1));

        iter.advance_cursor(); // j -> 2
        assert_eq!(iter.cursor(), 1);

        iter.advance_cursor(); // j -> 3
        assert_eq!(iter.cursor(), 2);

        iter.advance_cursor(); // j -> 4
        assert_eq!(iter.cursor(), 3);

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));
    }

    #[test]
    fn check_advance_chain() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore(); // j -> 1

        assert_eq!(iter.cursor(), 0);

        iter.advance_cursor() // j -> 2
            .advance_cursor() // j -> 3
            .advance_cursor(); // j -> 4

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));
    }

    #[test]
    fn check_move_previous() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore(); // j -> 1

        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek(), Some(&&1));

        iter.advance_cursor(); // j -> 2
        assert_eq!(iter.cursor(), 1);

        let _ = iter.move_cursor_back(); // j -> 1
        assert_eq!(iter.cursor(), 0);

        iter.advance_cursor(); // j -> 2
        assert_eq!(iter.cursor(), 1);

        let _ = iter.move_cursor_back(); // j -> 1
        assert_eq!(iter.cursor(), 0);

        iter.advance_cursor(); // j -> 2
        assert_eq!(iter.cursor(), 1);

        iter.advance_cursor() // j -> 3
            .advance_cursor(); // j -> 4

        assert_eq!(iter.cursor(), 3);

        let v4 = iter.peek();
        assert_eq!(v4, Some(&&4));

        let _ = iter.move_cursor_back().and_then(|it| {
            it.move_cursor_back() // j -> 3
                .and_then(|it| {
                    it.move_cursor_back() // j -> 2
                        .and_then(|it| it.move_cursor_back())
                })
        }); // j -> 1

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));

        let prev = iter.move_cursor_back();
        assert!(prev.is_err());

        let v1 = iter.peek();
        assert_eq!(v1, Some(&&1));
    }

    #[test]
    fn test_with_inherited_feature_count() {
        let iterable = [1, 2, 3];
        let mut iter = iterable.iter().peekmore();

        iter.advance_cursor();
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

        iter.advance_cursor(); // j = 2
        iter.advance_cursor(); // j = 3
        let value = iter.peek().unwrap(); // 3
        assert_eq!(value, &&3);

        let peek = iter.peek_previous(); // 2
        assert_eq!(peek.unwrap(), Some(&&2));
        assert_eq!(iter.cursor(), 1);

        let peek = iter.peek_previous(); // 1
        assert_eq!(peek.unwrap(), Some(&&1));
        assert_eq!(iter.cursor(), 0);

        let peek = iter.peek_previous();
        assert_eq!(peek, Err(PeekMoreError::ElementHasBeenConsumed));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn peek_previous_beyond_none() {
        let iterable = [1];
        let mut iter = iterable.iter().peekmore(); // j = 1
        assert_eq!(iter.cursor(), 0);

        iter.advance_cursor(); // j = None (1)
        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 1);

        iter.advance_cursor(); // j = None (2)
        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 2);

        iter.advance_cursor(); // j = None (3)
        let peek = iter.peek(); // current
        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 3);

        let peek = iter.peek_previous(); // None (2)
        assert_eq!(peek.unwrap(), None);
        assert_eq!(iter.cursor(), 2);

        let peek = iter.peek_previous(); // None (1)
        assert_eq!(peek.unwrap(), None);
        assert_eq!(iter.cursor(), 1);

        let peek = iter.peek_previous(); // 1
        assert_eq!(peek.unwrap(), Some(&&1));
        assert_eq!(iter.cursor(), 0);

        let peek = iter.peek_previous();
        assert_eq!(peek, Err(PeekMoreError::ElementHasBeenConsumed));
        assert_eq!(iter.cursor(), 0);

        let peek = iter.peek_previous();
        assert_eq!(peek, Err(PeekMoreError::ElementHasBeenConsumed));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_forward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let _ = iter.advance_cursor_by(3);
        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 6);
    }

    #[test]
    fn check_move_backward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let result = iter.move_cursor_back_by(2);
        assert!(result.is_ok());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&2));
        assert_eq!(iter.cursor(), 1);

        let result = iter.move_cursor_back_by(1);
        assert!(result.is_ok());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);

        let result = iter.move_cursor_back_by(1);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_backward_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let result = iter.move_cursor_back_by(5);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);
    }

    #[test]
    fn check_move_backward_or_reset() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let _ = iter.move_cursor_back_or_reset(2);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&2));
        assert_eq!(iter.cursor(), 1);

        let _ = iter.move_cursor_back_or_reset(1);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);

        let _ = iter.move_cursor_back_or_reset(1);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_backward_or_reset_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let _ = iter.move_cursor_back_or_reset(5);
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_backward_or_reset_empty() {
        let iterable = "".chars();

        let mut iter = iterable.peekmore();

        assert_eq!(iter.peek(), None);
        assert_eq!(iter.cursor(), 0);

        let _ = iter.move_cursor_back_or_reset(5);

        assert_eq!(iter.peek(), None);
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_peek_forward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let peek = iter.peek_forward(3);

        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let peek = iter.peek_forward(3);
        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 6);
    }

    #[test]
    fn check_peek_backward() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let result = iter.peek_backward(2);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Some(&&2));
        assert_eq!(iter.cursor(), 1);

        let result = iter.peek_backward(1);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Some(&&1));
        assert_eq!(iter.cursor(), 0);

        let result = iter.peek_backward(1);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_peek_backward_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let result = iter.peek_backward(5);
        assert!(result.is_err());
        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);
    }

    #[test]
    fn check_peek_backward_or_first_beyond_consumed_verify_cursor_position() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_by(3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);

        let peek = iter.peek_backward_or_first(5);
        assert_eq!(peek, Some(&&1));
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_peek_backward_or_first_empty() {
        let iterable = "".chars();

        let mut iter = iterable.peekmore();

        assert_eq!(iter.peek(), None);
        assert_eq!(iter.cursor(), 0);

        let peek = iter.peek_backward_or_first(5);

        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_forward_while() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_while(|i| **i.unwrap() != 3);

        let peek = iter.peek();
        assert_eq!(peek, Some(&&2));
        assert_eq!(iter.cursor(), 1);
    }

    #[test]
    fn check_move_forward_while_empty() {
        let iterable: [i32; 0] = [];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_while(|i| if let Some(i) = i { **i != 3 } else { false });

        let peek = iter.peek();
        assert_eq!(peek, None);
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_forward_while_some() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        let _ = iter.advance_cursor_while(|i| i.is_some());

        let peek = iter.peek();
        assert_eq!(peek, Some(&&4));
        assert_eq!(iter.cursor(), 3);
    }

    #[test]
    fn check_peek_nth() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek_nth(0), Some(&&1));
        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek_nth(1), Some(&&2));
        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek_nth(2), Some(&&3));
        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek_nth(3), Some(&&4));
        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek_nth(4), None);
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_peek_nth_empty() {
        let iterable: [i32; 0] = [];

        let mut iter = iterable.iter().peekmore();

        assert_eq!(iter.peek_nth(0), None);
        assert_eq!(iter.cursor(), 0);
        assert_eq!(iter.peek_nth(1), None);
        assert_eq!(iter.cursor(), 0);
    }

    #[test]
    fn check_move_nth() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        iter.move_nth(20);
        assert_eq!(iter.peek_nth(0), Some(&&1));
        assert_eq!(iter.cursor(), 20);
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
        assert_eq!(iter.cursor(), 0);

        iter.move_nth(10);
        assert_eq!(iter.cursor(), 10);
    }

    #[test]
    fn truncate_iterator_to_cursor_is_noop_when_queue_is_empty_from_no_peeking() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert!(iter.queue.is_empty());

        iter.truncate_iterator_to_cursor();

        assert!(iter.queue.is_empty());
        assert_eq!(iter.peek(), Some(&&1));
        assert!(!iter.queue.is_empty());
    }

    #[test]
    fn truncate_iterator_to_cursor_is_noop_when_queue_is_empty_from_iteration() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().peekmore();

        assert!(iter.queue.is_empty());

        iter.peek_forward(2);
        iter.next();
        iter.next();
        iter.next();

        assert!(iter.queue.is_empty());

        iter.truncate_iterator_to_cursor();

        assert!(iter.queue.is_empty());
        assert_eq!(iter.peek(), Some(&&4));
        assert!(!iter.queue.is_empty());
    }

    #[test]
    fn truncate_to_iterator_fill_queue() {
        let mut iter = [0, 1, 2, 3].iter().peekmore();
        iter.advance_cursor();
        iter.truncate_iterator_to_cursor();

        let value = **iter.peek().unwrap();

        assert_eq!(value, 1);
    }

    #[test]
    fn truncate_to_iterator_on_empty_collection() {
        let mut iter = core::iter::empty::<i32>().peekmore();
        iter.advance_cursor();
        assert_eq!(iter.cursor, 1);

        iter.truncate_iterator_to_cursor();
        assert_eq!(iter.cursor, 0);

        assert!(iter.peek().is_none());
    }

    #[test]
    fn truncate_to_iterator_on_single_element_collection() {
        let mut iter = core::iter::once(0).peekmore();
        assert_eq!(*iter.peek().unwrap(), 0);
        assert_eq!(iter.cursor, 0);

        iter.advance_cursor(); // starts at 0, so now is 1 (i.e. second element so None)
        assert_eq!(iter.cursor, 1);
        assert!(iter.peek().is_none());

        iter.truncate_iterator_to_cursor();
        assert_eq!(iter.cursor, 0);

        assert!(iter.peek().is_none());
    }

    #[test]
    fn truncate_to_iterator_cursor_and_queue_equal_length() {
        let mut iter = [0, 1, 2, 3].iter().peekmore();
        iter.peek();
        iter.advance_cursor();
        iter.truncate_iterator_to_cursor();

        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn peek_range_from_start_smaller_than_input_len() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_range(0, 2);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
        assert_eq!(view.len(), 2);
    }

    #[test]
    fn peek_range_from_start_eq_to_input_len() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_range(0, 4);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
        assert_eq!(view[2], Some(&2));
        assert_eq!(view[3], Some(&3));
        assert_eq!(view.len(), 4);
    }

    #[test]
    fn peek_range_from_start_bigger_than_input_len() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_range(0, 6);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
        assert_eq!(view[2], Some(&2));
        assert_eq!(view[3], Some(&3));
        assert_eq!(view[4], None);
        assert_eq!(view[5], None);
        assert_eq!(view.len(), 6);
    }

    #[test]
    fn peek_range_from_middle() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_range(2, 5);

        assert_eq!(view[0], Some(&2));
        assert_eq!(view[1], Some(&3));
        assert_eq!(view[2], None);
        assert_eq!(view.len(), 3);
    }

    #[test]
    fn peek_range_out_of_bounds() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_range(5, 6);

        assert_eq!(view[0], None);
        assert_eq!(view.len(), 1);
    }

    #[test]
    fn peek_range_empty() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_range(0, 0);

        assert_eq!(view.len(), 0);
    }

    #[test]
    fn peek_range_match() {
        let mut peeking_queue = ["call", "f", "1"].iter().peekmore();
        let view = peeking_queue.peek_range(1, 3);

        let value = match view {
            [Some(&"f"), Some(arg)] => arg,
            _ => panic!("test case peek_range_match failed"),
        };

        assert_eq!(**value, "1");
        assert_eq!(view.len(), 2);
    }

    #[test]
    #[should_panic]
    fn peek_range_panic_on_invalid_range() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let _ = peeking_queue.peek_range(2, 1);
    }
}
