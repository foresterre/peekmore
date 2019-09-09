#![no_std]

extern crate alloc;

use alloc::vec::Vec;

/// Trait which allows one to create an iterator which allows us to peek multiple times forward.
pub trait CreateLookAheadIterator: Iterator + Sized {
    /// Create an iterator where we can look (peek) forward multiple times from an existing iterator.
    fn look_ahead(self) -> LookAheadIterator<Self>;
}

impl<I: Iterator> CreateLookAheadIterator for I {
    fn look_ahead(self) -> LookAheadIterator<I> {
        LookAheadIterator {
            iterator: self,
            queue: Vec::new(),
            needle: None,
        }
    }
}

/// This iterator allows us to peek multiple times without consuming a value.
/// In reality the underlying iterator will be consumed, but the values will be stored in a local
/// vector. This vector allows us to move the frame which we can see.
#[derive(Debug)]
pub struct LookAheadIterator<I: Iterator> {
    /// Inner iterator. Consumption of this iterator does not represent consumption of the LookAheadIterator.
    iterator: I,

    /// The queue represent the items of our LookAheadIterator which have not been consumed, but have been
    /// prepared to view ('peek') without consuming them. Once an element is consumed, we can no longer
    /// view an item in the queue.
    queue: Vec<Option<I::Item>>,

    /// The needle helps us determine which item we currently have in view.
    /// If the needle is None, we have not advanced (or have reset) our window.
    needle: Option<usize>,
}

/// Adds functions which enable non-consuming viewing of non-consumed elements of an iterator.
pub trait LookAheadView<I: Iterator> {
    // methods to preview the next non consumed elements of the iterator

    /// Get the reference of our current value preview.
    /// Note that if we have not advanced our position yet, our view will return None, even if
    /// the underlying iterator does contain values, and thus is not empty.
    fn preview(&mut self) -> Option<&I::Item>;

    /// Advance the view to the next frame and return a reference to its value.
    fn preview_next(&mut self) -> Option<&I::Item>;

    // methods to control our view

    /// Advance the peekable view.
    /// This does not advance the iterator itself.
    /// To advance the iterator, use `Iterator::next()`.
    fn advance_view(&mut self) -> &mut Self;

    /// Reset the view. If we call [crate::multi_peek::LookAheadView::preview] just after a reset,
    /// it will return None again. The view will have to be advanced once for a non empty iterator to
    /// show a value again.
    fn reset_view(&mut self);
}

impl<I: Iterator> LookAheadView<I> for LookAheadIterator<I> {
    fn preview(&mut self) -> Option<&I::Item> {
        if let Some(needle) = self.needle {
            self.queue.get(needle).and_then(|v| v.as_ref())
        } else {
            None
        }
    }

    // convenient as we don't have to re-assign our mutable borrow on the 'user' side.
    fn preview_next(&mut self) -> Option<&I::Item> {
        let this = self.advance_view();
        this.preview()
    }

    fn advance_view(&mut self) -> &mut LookAheadIterator<I> {
        match self.needle {
            None if self.queue.is_empty() => {
                self.push_next_to_queue();
            }
            Some(pos) if pos + 1 >= self.queue.len() => {
                self.push_next_to_queue();
            }
            _ => {}
        }
        self.increment_needle();
        self
    }

    fn reset_view(&mut self) {
        self.needle = None;
    }
}

impl<I: Iterator> LookAheadIterator<I> {
    /// Consume the underlying iterator and push an element to the queue.
    fn push_next_to_queue(&mut self) {
        let item = self.iterator.next();
        self.queue.push(item);
    }

    /// Increment the needle which points to the current peekable item.
    /// Note: if used incorrectly can cause integer underflow.
    fn increment_needle(&mut self) {
        if let Some(needle) = self.needle {
            self.needle = Some(needle + 1)
        } else {
            self.needle = Some(0)
        }
    }

    /// Decrement the needle which points to the current peekable item.
    /// Note: if used incorrectly can cause integer underflow.
    fn decrement_needle(&mut self) {
        if let Some(needle) = self.needle {
            // do not underflow
            if needle > 0 {
                self.needle = Some(needle - 1)
            }
        }
    }
}

impl<'a, I: Iterator> Iterator for LookAheadIterator<I> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peek_forward_with_reassignment() {
        let iterable = [1, 2, 3, 4];

        let mut peek = iterable.iter().look_ahead();

        assert_eq!(peek.preview(), None);

        let peek = peek.advance_view();
        assert_eq!(peek.preview(), Some(&&1));

        let peek = peek.advance_view();
        assert_eq!(peek.preview(), Some(&&2));

        let peek = peek.advance_view();
        assert_eq!(peek.preview(), Some(&&3));

        let peek = peek.advance_view();
        assert_eq!(peek.preview(), Some(&&4));

        let peek = peek.advance_view();
        assert_eq!(peek.preview(), None);
    }

    #[test]
    fn peek_forward_without_reassignment_separately_advance_and_peek() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().look_ahead();

        assert_eq!(iter.preview(), None);

        let v1 = iter.advance_view().preview();
        assert_eq!(v1, Some(&&1));

        let v2 = iter.advance_view().preview();
        assert_eq!(v2, Some(&&2));

        let v3 = iter.advance_view().preview();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.advance_view().preview();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.advance_view().preview();
        assert_eq!(v5, None);
    }

    #[test]
    fn peek_forward_without_reassignment_advance_and_peek_combined() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().look_ahead();

        assert_eq!(iter.preview(), None);

        let v1 = iter.preview_next();
        assert_eq!(v1, Some(&&1));

        let v2 = iter.preview_next();
        assert_eq!(v2, Some(&&2));

        let v3 = iter.preview_next();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.preview_next();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.preview_next();
        assert_eq!(v5, None);
    }

    #[test]
    fn peek_forward_without_reassignment_advance_and_peek_combined_and_reset_view() {
        let iterable = [1, 2, 3, 4];

        let mut iter = iterable.iter().look_ahead();

        assert_eq!(iter.preview(), None);

        let v1 = iter.preview_next();
        assert_eq!(v1, Some(&&1));

        let v2 = iter.preview_next();
        assert_eq!(v2, Some(&&2));

        let _ = iter.reset_view();
        assert_eq!(iter.preview(), None);

        let v1again = iter.preview_next();
        assert_eq!(v1again, Some(&&1));

        let v2again = iter.preview_next();
        assert_eq!(v2again, Some(&&2));

        let v3 = iter.preview_next();
        assert_eq!(v3, Some(&&3));

        let v4 = iter.preview_next();
        assert_eq!(v4, Some(&&4));

        let v5 = iter.preview_next();
        assert_eq!(v5, None);
    }

    #[test]
    fn empty() {
        let iterable: [i32; 0] = [];

        let mut iter = iterable.iter().look_ahead();

        assert_eq!(iter.preview(), None);

        let none = iter.preview_next();
        assert_eq!(none, None);

        let iter = iter.advance_view();
        assert_eq!(iter.preview(), None);
        assert_eq!(iter.preview_next(), None);
    }

    #[test]
    fn test_with_consume() {
        let iterable = "123".chars();

        let mut iter = iterable.look_ahead();
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(1, 10).unwrap())
        );
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(2, 10).unwrap())
        );
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(3, 10).unwrap())
        );
        assert_eq!(iter.preview_next(), None);
        assert_eq!(iter.next(), Some(core::char::from_digit(1, 10).unwrap()));
        assert_eq!(iter.next(), Some(core::char::from_digit(2, 10).unwrap()));
        assert_eq!(iter.next(), Some(core::char::from_digit(3, 10).unwrap()));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.preview_next(), None);
    }

    #[test]
    fn test_with_consume_and_reset() {
        let iterable = "456".chars();

        let mut iter = iterable.look_ahead();
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(4, 10).unwrap())
        );
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(5, 10).unwrap())
        );
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(6, 10).unwrap())
        );
        assert_eq!(iter.preview_next(), None);
        assert_eq!(iter.next(), Some(core::char::from_digit(4, 10).unwrap()));
        iter.reset_view();

        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(5, 10).unwrap())
        );
        assert_eq!(
            iter.preview_next(),
            Some(&core::char::from_digit(6, 10).unwrap())
        );

        assert_eq!(iter.next(), Some(core::char::from_digit(5, 10).unwrap()));
        assert_eq!(iter.next(), Some(core::char::from_digit(6, 10).unwrap()));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.preview_next(), None);
    }
}
