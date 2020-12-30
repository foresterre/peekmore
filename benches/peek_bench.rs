// A first benchmark for peekmore
// The outcomes should not be relied upon (yet)
//
// TODO: improve benchmark suite

use criterion::black_box;
use criterion::Criterion;
use criterion::{criterion_group, criterion_main};
use peekmore::{PeekMore, PeekMoreIterator};

fn peek_at<I: Iterator>(
    mut iterator: PeekMoreIterator<I>,
    peek_at: impl IntoIterator<Item = usize>,
) {
    for i in peek_at {
        let _ = iterator.peek_nth(i);
        iterator.truncate_iterator_to_cursor();
    }
}

const AMOUNT: usize = 10_000;
const PEEK_STEP: usize = 4;
const PEEK_TIMES: usize = AMOUNT / PEEK_STEP;

fn peek_nth_benchmark(c: &mut Criterion) {
    c.bench_function("peek_nth", move |b| {
        b.iter(|| {
            peek_at(
                black_box((0..AMOUNT).peekmore()),
                (0..PEEK_TIMES).map(|n| n * PEEK_STEP),
            )
        });
    });
}

criterion_group!(benches, peek_nth_benchmark);
criterion_main!(benches);
