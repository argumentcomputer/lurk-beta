use blstrs::Scalar as Fr;
use criterion::{black_box, criterion_group, criterion_main, Criterion, SamplingMode};
use lurk::{
    eval::lang::{Coproc, Lang},
    proof::groth16::Groth16Prover,
    proof::nova,
};
use std::sync::Arc;
use std::time::Duration;

const DEFAULT_REDUCTION_COUNT: usize = 10;

fn public_params_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("public_params_benchmark");
    group.sampling_mode(SamplingMode::Flat);
    let lang_bls = Lang::<Fr, Coproc<Fr>>::new();
    let lang_bls_rc = Arc::new(lang_bls);
    let lang_pallas =
        Lang::<pasta_curves::pallas::Scalar, Coproc<pasta_curves::pallas::Scalar>>::new();
    let lang_pallas_rc = Arc::new(lang_pallas);

    let reduction_count = DEFAULT_REDUCTION_COUNT;

    group.bench_function("public_params_nova", |b| {
        b.iter(|| {
            let result = nova::public_params(reduction_count, lang_pallas_rc.clone());
            black_box(result)
        })
    });

    group.bench_function("public_params_groth", |b| {
        b.iter(|| {
            let result =
                Groth16Prover::create_groth_params(DEFAULT_REDUCTION_COUNT, lang_bls_rc.clone());
            black_box(result)
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .measurement_time(Duration::from_secs(120))
        .sample_size(10);
    targets = public_params_benchmark
}
criterion_main!(benches);
