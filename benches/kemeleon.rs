use criterion::{criterion_group, criterion_main, Criterion};
use ct_kemeleon::*;
use rand::thread_rng;

fn kemeleon1<const N: usize>(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    // First pick a vector that we know can be encoded
    let (v, encoded) = loop {
        let v = rand_vec::<N>(&mut rng);
        if let Some(e) = kemeleon1_encode(&mut rng, &v) {
            break (v, e);
        }
    };

    c.bench_function(&format!("kemeleon1_encode[N={N}]"), |b| {
        b.iter(|| kemeleon1_encode(&mut rng, &v))
    });

    // Do a separate bench to measure how long Kemeleon1 takes when you account for retries
    c.bench_function(&format!("kemeleon1_encode_with_reject[N={N}]"), |b| {
        b.iter(|| loop {
            let v = rand_vec::<N>(&mut rng);
            if kemeleon1_encode(&mut rng, &v).is_some() {
                break;
            }
        })
    });

    c.bench_function(&format!("kemeleon1_decode[N={N}]"), |b| {
        b.iter(|| kemeleon1_decode::<N>(&encoded))
    });
}

fn kemeleon2(c: &mut Criterion) {
    let mut rng = thread_rng();

    const N: usize = 256;
    let v = rand_vec::<N>(&mut rng);

    c.bench_function(&format!("kemeleon2_encode[N={N}]"), |b| {
        b.iter(|| kemeleon2_encode(&mut rng, &v))
    });
    let encoded = kemeleon2_encode(&mut rng, &v);

    c.bench_function(&format!("kemeleon2_decode[N={N}]"), |b| {
        b.iter(|| kemeleon2_decode::<N>(&encoded))
    });
}

fn all(c: &mut Criterion) {
    kemeleon2(c);
    kemeleon1::<128>(c);
    kemeleon1::<256>(c);
    kemeleon1::<512>(c);
    kemeleon1::<768>(c);
    kemeleon1::<1024>(c);
}

criterion_group!(benches, all);
criterion_main!(benches);
