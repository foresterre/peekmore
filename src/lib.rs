// #![no_std] // TODO enable
#![deny(missing_docs)]
#![deny(clippy::all)]

//! **Synopsis:**
//!
//! This crate introduces a multi-peekable iterator.
//! The iterator is similar to [`Peekable`]. The main difference is that [`Peekable`] only
//! allows you to peek at the next element and no further. When using `PeekMore` however,
//! you can peek at as many elements as you want.
//!
//! **A peek at how it works:**
//!
//! To enable peeking at multiple elements ahead of consuming a next element, the iterator uses a
//! traversable queue which holds the elements which you can peek at, but have not been
//! consumed (yet).
//! The underlying data structure of this queue can be a `Vec`, or a `SmallVec` from the smallvec crate.
//! By default, the `SmallVec` is used. SmallVec uses the stack for a limited amount of elements and
//! will only allocate on the heap if this maximum amount of elements is reached.
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
extern crate core;

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

/// Use a `Vec` to queue iterator elements if the `smallvec` feature is disabled.
#[cfg(not(feature = "smallvec"))]
use alloc::vec::Vec;
use core::fmt::Debug;
use std::ops::Deref;

/// Use a SmallVec to queue iterator elements instead of a Vec, if the `smallvec` feature is enabled
/// (default).
#[cfg(feature = "smallvec")]
use smallvec::SmallVec;

/// Trait which allows you to create the multi-peek iterator.
/// It allows you to peek at any unconsumed element.
/// Elements can be consumed using the [`next`] method defined on any [`Iterator`].
///
/// [`next`]: https://doc.rust-lang.org/core/iter/trait.Iterator.html#tymethod.next
/// [`Iterator`]: https://doc.rust-lang.org/core/iter/trait.Iterator.html
pub trait PeekMore: Iterator + Sized {
    /// Create a multi-peek iterator where we can peek forward multiple times from an existing iterator.
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
const DEFAULT_STACK_SIZE: usize = 8;

/// This iterator makes it possible to peek multiple times without consuming a value.
/// In reality the underlying iterator will be consumed, but the values will be stored in a queue.
/// This queue allows us to peek at unconsumed elements (as far as the multi-peek iterator is concerned).
/// When the iterator [consumes] an element, the element at the front of the queue will be dequeued,
/// and will no longer be peekable.
///
/// [consumes]: https://doc.rust-lang.org/core/iter/trait.Iterator.html#tymethod.next
#[derive(Clone, Debug)]
pub struct PeekMoreIterator<I: Iterator> {
    /// The underlying iterator. Consumption of this inner iterator does not represent consumption of the
    /// `PeekMoreIterator`.
    iterator: I,

    /// The queue represents the items of our iterator which have not been consumed, but can be peeked
    /// at without consuming them. Once an element has been consumed by the iterator, the element will
    /// be dequeued and it will no longer be possible to peek at this element.
    #[cfg(not(feature = "smallvec"))]
    queue: Vec<Option<I::Item>>,
    #[cfg(feature = "smallvec")]
    queue: SmallVec<[Option<I::Item>; DEFAULT_STACK_SIZE]>,

    /// The cursor points to the element we are currently peeking at.
    ///
    /// The cursor will point to the first unconsumed element if the value is `0`, the second if it is
    /// `1`, and so forth. Peeking at the 0th cursor element is equivalent to peeking with
    /// [`core::iter::Peekable::peek`].
    ///
    /// [`core::iter::Peekable::peek`]: https://doc.rust-lang.org/core/iter/struct.Peekable.html#method.peek
    cursor: usize,
}

impl<I: Iterator> PeekMoreIterator<I> {
    /// Get a reference to the element where the cursor currently points to. If no such element exists,
    /// return `None` will be returned.
    ///
    /// If we haven't advanced our cursor, it will point to the same element as `Iterator::next()` would
    /// return.
    /// Note that the cursor can't point to an element before the first unconsumed element within
    /// the iterator. In a sense the cursor moves independently within the iterator.
    /// But it can only point to unconsumed elements.
    ///
    /// The following illustration aims to show how `peek()` behaves. `i` represents the position
    /// of the iterator (i.e. the next value that will be returned if `next()` is called) and `j`
    /// represents the position of the cursor (i.e. the current element referenced if
    /// `peek()` is called).
    /// In example code next to the illustrations, the first element `1` is analogous to `A`,
    /// `2` to `B`, etc.
    ///
    /// The example below primarily uses `advance_cursor()` to move the cursor and `peek()` to
    /// peek at the element the cursor points to, but many often more convenient methods exist to
    /// change the element cursor points at, or to peek at those elements.
    ///
    /// * Let's start:
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
    /// * Call `peek()`:
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
    /// * Call `advance_cursor()`
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
    /// * Call `peek()`
    ///
    /// The reference returned by `peek()` will not change, similar to the behaviour of
    /// [`core::iter::Peekable::peek`]. In order to move to the next peekable element, we need to
    /// advance the cursor.
    ///
    /// ```rust
    /// # use peekmore::PeekMore;
    /// # let iterable = [1, 2, 3, 4];
    /// # let mut iterator = iterable.iter().peekmore();
    /// # let iter = iterator.advance_cursor();
    /// let j = iterator.peek();
    /// assert_eq!(j, Some(&&2));
    ///
    /// // Calling `peek()` multiple times doesn't shift the position of the cursor;
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
    /// * Call `next()`
    ///
    /// By calling next, the underlying iterator will be advanced andthe element represented by `A`
    /// will be consumed. It won't be possible to peek at `A` anymore.
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
    /// * Call `next()`.
    ///
    /// The underlying iterator is advanced again.
    /// As a result, the cursor position also shifts to the next iterator position, which happens if
    /// the underlying iterator consumed an element where our cursor pointed at (that is if `j < i`).
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

    /// Peeks at the first unconsumed element, regardless of where the cursor currently is.
    #[inline]
    pub fn peek_first(&mut self) -> Option<&I::Item> {
        self.peek_nth(0)
    }

    // Convenient as we don't have to re-assign our mutable borrow on the 'user' side.
    /// Advance the cursor to the next element and return a reference to that value.
    #[inline]
    pub fn peek_next(&mut self) -> Option<&I::Item> {
        let this = self.advance_cursor();
        this.peek()
    }

    /// Try to peek at a previous element. If no such element exists, an `Err` result containing a
    /// [`PeekMoreError::ElementHasBeenConsumed`] will be returned.
    ///
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
    /// can use the [`peek_backward_or_first`] method instead.
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

    /// Advance the cursor to the next peekable element.
    ///
    /// This method does not advance the iterator itself. To advance the iterator, call [`next()`]
    /// instead.
    ///
    /// A mutable reference to the iterator is returned, which allows the operation to be chained.
    ///
    /// [`next()`]: struct.PeekMoreIterator.html#impl-Iterator
    #[inline]
    pub fn advance_cursor(&mut self) -> &mut PeekMoreIterator<I> {
        self.increment_cursor();
        self
    }

    /// Advance the cursor `n` elements forward.
    ///
    /// This does not advance the iterator itself. To advance the iterator, call [`next()`] instead.
    ///
    /// [`next()`]: struct.PeekMoreIterator.html#impl-Iterator
    #[inline]
    pub fn advance_cursor_by(&mut self, n: usize) -> &mut PeekMoreIterator<I> {
        self.cursor += n;
        self
    }

    /// Moves the cursor forward until the predicate is no longer `true`.
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
    /// If such an element doesn't exist, a [`PeekMoreError::ElementHasBeenConsumed`] will be
    /// returned.
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
    /// cursor, an error will be returned instead. In case of an error, the cursor will stay at the position
    /// it pointed at prior to calling this method.
    ///
    /// If you want to reset the cursor to the first unconsumed element even if there aren't `n`
    /// unconsumed elements before the cursor position, the [`move_backward_or_reset`] method can be
    /// used.
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

    /// Move the cursor `n` elements backward, or reset its position to the first non-consumed element.
    /// The latter happens when the cursor position is smaller than the elements it has to move
    /// backwards by.
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

    /// Reset the position of the cursor.
    ///
    /// If [`peek`] is called just after a reset, it will return a reference to the first element.
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
                dbg!("filling queue!");
                self.push_next_to_queue()
            }
        }
    }

    /// Consume the underlying iterator and push an element to the queue.
    #[inline]
    fn push_next_to_queue(&mut self) {
        let item = self.iterator.next();
        dbg!(item.is_some());
        self.queue.push(item);
    }

    /// Increment the cursor which points to the current peekable item.
    /// Note: if the cursor is [core::usize::MAX], it will not increment any further.
    ///
    /// [core::usize::MAX]: https://doc.rust-lang.org/core/usize/constant.MAX.html
    #[inline]
    fn increment_cursor(&mut self) {
        // do not overflow
        self.cursor = self.cursor.saturating_add(1);
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

    /// Return the current cursor position.
    /// This is intended for use by code that more finely controls where the iterator resets to.
    #[inline]
    fn cursor(&self) -> usize {
        self.cursor
    }

    /// Ensures the queue is filled for `n` elements.
    #[inline]
    fn ensure_queue_is_filled(&mut self, n: usize) {
        if n > self.queue.len() {
            self.fill_queue(n);
        }
    }

    /// Remove all elements from the start of the iterator until reaching the same
    /// position as the cursor by calling `Iterator::next()`.
    ///
    /// After calling this method, `iter.peek() == iter.next().as_ref()`.
    ///
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
        if self.cursor < self.queue.len() {
            self.queue.drain(0..self.cursor);
        } else {
            // if the cursor is greater than the queue length,
            // we want to remove the overflow from the iterator
            for _ in 0..self.cursor.saturating_sub(self.queue.len()) {
                let _ = self.iterator.next();
            }
            self.queue.clear();
        }

        self.cursor = 0;
    }

    /// Returns a view into the next `start` (inclusive) to `end` (exclusive) elements.
    ///
    /// **Note:** `start` and `end` represent indices and start at `0`. These indices always start
    /// at the beginning of the queue (the unconsumed iterator) and don't take the position of the cursor
    /// into account.
    ///
    /// # Panics
    ///
    /// **Panics** if `start > end`, in which case the range would be negative.
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
    // why not `core::ops::RangeBound<T>`? it adds unnecessary complexity since we would need to define what
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
        self.ensure_queue_is_filled(end);

        // return a view of the selected range
        &self.queue.as_slice()[start..end]
    }

    /// Returns a view into the next `n` unconsumed elements of the iterator.
    ///
    /// Here, `n` represents the amount of elements as counted from the start of the unconsumed iterator.
    ///
    /// For example, if we created a (peekmore) iterator from the array `[1, 2, 3]` and consume the first
    /// element by calling the regular `Iterator::next` method, and then call `peek_amount(3)`, the iterator will
    /// return `&[Some(2), Some(3), None]`. Here `Some(2)` and `Some(3)` are queued elements which
    /// we can peek at, and are not consumed by the iterator yet. `None` is the last element returned by
    /// our view, since our original iterator is sized and doesn't contain more elements. Thus in the absence
    /// of additional elements, we return `None`. This method is a variation on [`peek_range`].
    /// You could instead have called `peek_range(0, n)` (note that `peek_range` takes indices as arguments
    /// instead of an amount).
    ///
    /// **Note:** This method does not use or modify the position of the cursor.
    ///
    /// # Example:
    ///
    /// ```
    /// use peekmore::PeekMore;
    ///
    /// let iterable = [1, 2, 3];
    /// let mut iter = iterable.iter().peekmore();
    ///
    /// match iter.peek_amount(4) { // -> &[Option(&1), Option(&2), Option(&3), None]
    ///   [Some(a), Some(b), Some(c), None] => println!("Found a match ({}, {}, {}) ", a, b, c),
    ///   _ => eprintln!("Expected (just) 3 more values"),
    /// }
    /// ```
    ///
    /// [`peek_range`]: struct.PeekMoreIterator.html#method.peek_range
    #[inline]
    pub fn peek_amount(&mut self, n: usize) -> &[Option<I::Item>] {
        self.peek_range(0, n)
    }

    /// Returns a view into the next `n` unconsumed elements of the iterator, **and** advances the
    /// cursor by `n` elements. Variation on [`peek_amount`], which also advances the cursor.
    ///
    /// `n` represents the amount of elements as counted from the start of the unconsumed iterator.
    ///
    /// **Note:** This method does modify the position of the cursor.
    ///
    /// # Example:
    ///
    /// ```
    /// use peekmore::PeekMore;
    ///
    /// let iterable = [1, 2, 3];
    /// let mut iter = iterable.iter().peekmore();
    ///
    /// assert_eq!(iter.peek_amount_and_advance(2), &[Some(&1), Some(&2)]);
    /// assert_eq!(iter.peek_amount_and_advance(2), &[Some(&3), None]);
    /// ```
    ///
    /// [`peek_range`]: struct.PeekMoreIterator.html#method.peek_range
    /// [`peek_amount`]: struct.PeekMoreIterator.html#method.peek_amount
    #[inline]
    pub fn peek_amount_and_advance(&mut self, n: usize) -> &[Option<I::Item>] {
        let end = self.cursor + n;

        // TODO consider name, as peek_amount does always peek (0, n), never peek (cursor, cursor + n),
        //  but not peeking from the cursor does hardly make any sense if we also advance the cursor
        //  every time.

        // fill the queue if we don't have enough elements
        self.ensure_queue_is_filled(end);

        dbg!(self.cursor, n, end);

        // advance the cursor
        self.advance_cursor_by(n);

        // return a view of the queue for the chosen amount of elements
        &self.queue.as_slice()[self.cursor..end]
    }


}

// TODO remove
impl<T: Debug, I: Iterator<Item = T>> PeekMoreIterator<I> {
    pub fn queue(&self) -> &[Option<<I as Iterator>::Item>] {
        self.queue.deref()
    }

    pub fn queue_mut(&mut self) -> &[Option<<I as Iterator>::Item>] {
        self.queue.deref()
    }
}

impl<I: Iterator> Iterator for PeekMoreIterator<I> {
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
    fn check_peek_first() {
        let iterable = [1, 2, 3, 4];
        let mut iter = iterable.iter().peekmore();

        // testing to make sure no matter where the cursor is, we always point
        // to the initial first element.
        assert_eq!(iter.peek_first(), Some(&&1));
        assert_eq!(iter.cursor(), 0);
        iter.increment_cursor();
        assert_eq!(iter.peek_first(), Some(&&1));
        assert_eq!(iter.cursor(), 1);
        iter.increment_cursor();
        assert_eq!(iter.peek_first(), Some(&&1));
        assert_eq!(iter.cursor(), 2);
        iter.increment_cursor();
        assert_eq!(iter.peek_first(), Some(&&1));
        assert_eq!(iter.cursor(), 3);
        iter.increment_cursor(); // try moving past the end too
        assert_eq!(iter.peek_first(), Some(&&1));

        // testing to ensure that it's the first *unconsumed* element of the iterator
        // and not the first of the iterable.
        iter.next();
        assert_eq!(iter.peek_first(), Some(&&2));
        iter.increment_cursor();
        assert_eq!(iter.peek_first(), Some(&&2));

        // testing at the end boundary of the iterable.
        iter.next(); // consume 2
        iter.next(); // consume 3
        assert_eq!(iter.peek_first(), Some(&&4));

        // test that if there's no unconsumed elements, it reports None.
        iter.next();
        assert_eq!(iter.peek_first(), None);
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
    fn truncate_to_iterator_cursor_less_than_queue_length() {
        let mut iter = [0, 1, 2, 3].iter().peekmore();
        iter.peek_nth(2);
        iter.truncate_iterator_to_cursor();

        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);

        let mut iter = [0, 1, 2, 3].iter().peekmore();
        iter.peek_nth(3);
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

    #[test]
    fn peek_amount_from_start_smaller_than_input_len() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_amount(2);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
        assert_eq!(view.len(), 2);
    }

    #[test]
    fn peek_amount_from_start_eq_to_input_len() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_amount(4);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
        assert_eq!(view[2], Some(&2));
        assert_eq!(view[3], Some(&3));
        assert_eq!(view.len(), 4);
    }

    #[test]
    fn peek_amount_from_start_bigger_than_input_len() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_amount(6);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
        assert_eq!(view[2], Some(&2));
        assert_eq!(view[3], Some(&3));
        assert_eq!(view[4], None);
        assert_eq!(view[5], None);
        assert_eq!(view.len(), 6);
    }

    #[test]
    fn peek_amount_empty() {
        let empty: [u32; 0] = [];
        let mut peeking_queue = empty.iter().peekmore();
        let view = peeking_queue.peek_amount(3);

        assert_eq!(view[0], None);
        assert_eq!(view[0], None);
        assert_eq!(view[0], None);
        assert_eq!(view.len(), 3);
    }

    #[test]
    fn peek_amount_zero() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_amount(0);

        assert_eq!(view.len(), 0);
    }

    #[test]
    fn peek_amount_match() {
        let mut peeking_queue = ["call", "f", "1"].iter().peekmore();
        let view = peeking_queue.peek_amount(4);

        let value = match view {
            [Some(&"call"), Some(&"f"), Some(arg), None] => arg,
            _ => panic!("test case peek_n_match failed"),
        };

        assert_eq!(**value, "1");
        assert_eq!(view.len(), 4);
    }

    #[test]
    fn peek_amount_renewed_view() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        let view = peeking_queue.peek_amount(2);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));

        let _removed = peeking_queue.next();

        let view = peeking_queue.peek_amount(2);

        assert_eq!(view[0], Some(&1));
        assert_eq!(view[1], Some(&2));
    }

    #[test]
    fn peek_amount_with_incremented_cursor() {
        let mut peeking_queue = [0, 1, 2, 3].iter().peekmore();
        peeking_queue.advance_cursor_by(2);
        assert_eq!(peeking_queue.cursor(), 2);

        // Despite incrementing the cursor, the `peek_amount` method always presents a view from the start
        // of the queue; i.e. the unconsumed elements.
        let view = peeking_queue.peek_amount(2);

        assert_eq!(view[0], Some(&0));
        assert_eq!(view[1], Some(&1));
    }

    #[test]
    fn peek_amount_and_advance() {
        let mut peeking_queue = [0].iter().peekmore();

        dbg!(&peeking_queue);

        let _ = peeking_queue.peek_amount_and_advance(2);

        dbg!(&peeking_queue);

        // assert_eq!(view[0], Some(&0));
        // assert_eq!(view[1], None);
        assert_eq!(peeking_queue.cursor(), 2);

        dbg!(peeking_queue.queue_mut());



        //
        // let view = peeking_queue.peek_amount_and_advance(2);
        // assert_eq!(view, &[None, None]);
    }
}
