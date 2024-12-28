use criterion::{criterion_group, criterion_main, Criterion};
use ct_kemeleon::*;

fn encode_decode_with_n<const N: usize>(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    // First pick a vector that we know can be encoded
    let (v, encoded) = loop {
        let v = rand_vec::<N>(&mut rng);
        if let Some(e) = vector_encode(&mut rng, &v) {
            break (v, e);
        }
    };

    c.bench_function(&format!("encode[N={N}]"), |b| {
        b.iter(|| vector_encode(&mut rng, &v))
    });

    c.bench_function(&format!("decode[N={N}]"), |b| {
        b.iter(|| vector_decode::<N>(&encoded))
    });
}

fn all(c: &mut Criterion) {
    encode_decode_with_n::<128>(c);
    encode_decode_with_n::<256>(c);
    encode_decode_with_n::<512>(c);
    encode_decode_with_n::<768>(c);
    encode_decode_with_n::<1024>(c);
}

criterion_group!(benches, all);
criterion_main!(benches);
