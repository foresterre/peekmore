test:
    cargo test --all

bench:
    cargo bench
    cargo bench --features smallvec

before-push:
    cargo fmt --all
    cargo clippy --all-targets --all-features -- -D warnings
    cargo test --all