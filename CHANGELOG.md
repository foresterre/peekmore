# Changelog

This is the changelog for [peekmore](https://github.com/foresterre/peekmore), a multi-peek variant of Rust's
[Peekable](https://doc.rust-lang.org/std/iter/struct.Peekable.html) iterator adapter.

If you found an issue, have a suggestion or want to provide feedback or insights, please feel free to open an issue on
the [issue tracker](https://github.com/foresterre/peekmore/issues).

## [Unreleased]

<!-- unreleased -->

[Unreleased]: https://github.com/foresterre/cargo-msrv

## [1.2.1] - 2023-04-11

### Fixed

* Fix issue with `advance_cursor_while`, where cursor would incorrectly be decremented  #72 #73

[1.2.1]: https://github.com/foresterre/peekmore/releases/tag/v1.2.1



## [1.2.0] - 2022-03-16

### Added

* Added `PeekMoreIterator::cursor` method #69 #71

[1.2.0]: https://github.com/foresterre/peekmore/releases/tag/v1.2.0

## [1.1.0] - 2022-02-18

### Added

* Added `PeekMoreIterator::peek_first` method #61

### Fixed

* Fix `PeekMoreIterator::truncate_iterator_to_cursor` #65

[1.1.0]: https://github.com/foresterre/peekmore/releases/tag/v1.1.0

## [1.0.0] - 2020-12-30

### Changed

* Rename peek_n to peek_amount
* Updated smallvec to 1.5.0
* Disable smallvec by default, can still be used by opting in with --feature smallvec

[1.0.0]: https://github.com/foresterre/peekmore/releases/tag/v1.0.0
