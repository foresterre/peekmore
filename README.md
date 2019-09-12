# peekmore

This crate introduces a multi-peekable iterator.
The iterator is similar to [core::iterator::Peekable](https://doc.rust-lang.org/core/iter/struct.Peekable.html). 
The main difference is that Peekable only allows you to peek at the next element and no further.
This crate aims to take that limitation away.

The documentation can be found at [docs.rs/peekmore](https://docs.rs/peekmore/).

### Usage example:

```rust
use peekmore::{CreatePeekMoreIterator, PeekView};

let iterable = [1, 2, 3, 4];
let mut iter = iterable.iter().peekmore();

// Peek at the first element.
let v1 = iter.peek();
assert_eq!(v1, Some(&&1));

// Consume the first element.
let v1c = iter.next();
assert_eq!(v1c, Some(&1));

// Peek at the second element (the element in our peek view also moved to the second element,
// since the first element was consumed.)
let v2 = iter.peek();
assert_eq!(v2, Some(&&2));

// Advance the peek view. The peek view will now be at the third element.
let _ = iter.advance_view();

// Check that it is indeed at the third element.
let v3 = iter.peek();
assert_eq!(v3, Some(&&3));

// Reset our peek view to the second element (since the first element has been consumed).
// It is the first non-consumed element.
iter.reset_view();

// Check that we are indeed at the second element again.
let v2 = iter.peek();
assert_eq!(v2, Some(&&2));

// Shift the peek view to the right twice by chaining the advance_view method.
let _ = iter.advance_view().advance_view();

// Verify that the peek view is indeed at the fourth element.
let v4 = iter.peek();
assert_eq!(v4, Some(&&4));

// Reset the view again.
iter.reset_view();

//We can also shift the peek view and peek with a single operation.
let v3 = iter.peek_next();
assert_eq!(v3, Some(&&3));
```

### Illustrated example

The following illustrated example aims to show how `peek()` behaves. Here, `i` represents the position
of the iterator (i.e. the next value that will be returned if `next()` is called) and `j`
represents the position of the current peek view (i.e. the current element referenced if
`peek()` is called).

* start:

```rust
use peekmore::{CreatePeekMoreIterator, PeekView};

// initialize our iterator
let iterable = [1, 2, 3, 4];
let mut iterator = iterable.iter().peekmore();
```

```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
 ^
 i, j
```

* call `peek()`:

```rust
let j = iterator.peek();
assert_eq!(j, Some(&&1));
```

```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
  ^
  i, j

peek() => Some(&&1)

```

* call `advance_view()`

```rust
let iter = iterator.advance_view();
```

```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
  ^         ^
  i         j
```

* call `peek()`
_or_ `peek(); peek()`  _or_ `peek(); peek(); peek()` etc.

(The reference returned by `peek()` will not change, similar to the behaviour of [`core::iter::Peekable::peek`]
  In order to move to the next peekable element, we need to advance our view.)

```rust
let j = iterator.peek();
assert_eq!(j, Some(&&2));

// calling peek() multiple times doesn't shift our peek view; a reference to the same element will be returned each call.
assert_eq!(iterator.peek(), Some(&&2));
assert_eq!(iterator.peek(), Some(&&2));
```

```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
  ^         ^
  i         j

          peek() => Some(&&2)
          peek() => Some(&&2)
          peek() => Some(&&2)  
```


* call `next()`
 (i.e. advance the iterator; the first element will be consumed)

```rust
let i = iterator.next();
assert_eq!(i, Some(&1));
```

```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
            ^
            i, j

next() => Some(&1)
```

* call `next()`.
 (i.e. advance the iterator again; we'll see that the current peek view shifts with the
  next iterator position if the iterator consumes elements where our peek view pointed at
  previously (`j < i`))


```rust
// show that the peek view still is at element 2.
let j = iterator.peek();
assert_eq!(j, Some(&&2));

// consume the second element
let i = iterator.next();
assert_eq!(i, Some(&2));

// while our peek view was at positioned at the second element. it is now at the third,
// since the iterator consumed the second.
let j = iterator.peek();
assert_eq!(j, Some(&&3));


```

```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
                       ^
                       i, j

          peek() => Some(&&2)
          next() => Some(&2)
                    peek() => Some(&&3)
```

* Consume more elements by calling `next()` until we reach `None`:

```rust
let i = iterator.next();
assert_eq!(i, Some(&3));

let j = iterator.peek();
assert_eq!(j, Some(&&4));

let i = iterator.next();
assert_eq!(i, Some(&4));

let j = iterator.peek();
assert_eq!(j, None);

let i = iterator.next();
assert_eq!(i, None);
```


```txt
-----     -----      -----     -----
| 1 | --> | 2 |  --> | 3 | --> | 4 | --> None --> None --> ...
-----     -----      -----     -----
                                           ^
                                           i, j
                      
                      next() => Some(&3)
                                peek() => Some(&&4)
                                next() => Some(&4)
                                         peek() => None
                                         next() => None
```

Experimental.