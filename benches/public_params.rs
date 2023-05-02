use blstrs::Scalar as Fr;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lurk::{
    eval::lang::{Coproc, Lang},
    proof::groth16::Groth16Prover,
    proof::nova,
};
use std::time::Duration;

const DEFAULT_REDUCTION_COUNT: usize = 10;

fn public_params_benchmark(c: &mut Criterion) {
    let lang_bls = Lang::<Fr, Coproc<Fr>>::new();
    // let lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();

    let reduction_count = DEFAULT_REDUCTION_COUNT;

    c.bench_function("public_params_nova", |b| {
        b.iter(|| {
            let result = nova::public_params(reduction_count, &lang_vesta);
            black_box(result)
        })
    });

    c.bench_function("public_params_groth", |b| {
        b.iter(|| {
            let result = Groth16Prover::create_groth_params(DEFAULT_REDUCTION_COUNT, &lang_bls);
            black_box(result)
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .measurement_time(Duration::from_secs(120))
        .sample_size(1);
    targets = public_params_benchmark
}
criterion_main!(benches);
