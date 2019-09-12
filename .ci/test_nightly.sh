.ci/test.sh
cargo +nightly build --verbose --all --features smallvec
cargo +nightly test --verbose --all --features smallvec