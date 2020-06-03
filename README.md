# peekmore

This crate introduces a multi-peekable iterator.
The iterator is similar to [core::iterator::Peekable](https://doc.rust-lang.org/core/iter/struct.Peekable.html). 
The main difference is that Peekable only allows you to peek at the next element and no further.
This crate aims to take that limitation away.

The documentation and more extensive example usage can be found at [docs.rs/peekmore](https://docs.rs/peekmore/).

### Usage example:

```rust
use peekmore::PeekMore;

fn main() {
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

```

### License
 
Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

#### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.