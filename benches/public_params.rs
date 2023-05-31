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

/// To run these benchmarks, do `cargo criterion public_params_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion public_params_benchmark --features flamegraph -- --profile-time <secs>```
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

cfg_if::cfg_if! {
    if #[cfg(feature = "flamegraph")] {
        // In order to collect a flamegraph, you need to indicate a profile time, see
        // https://github.com/tikv/pprof-rs#integrate-with-criterion
        // Example usage :
        // cargo criterion --bench public_params --features flamegraph -- --profile-time 5
        // Warning: it is not recommended to run this on an M1 Mac, as making pprof work well there is hard.
        criterion_group! {
            name = benches;
            config = Criterion::default()
                .with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
            targets = public_params_benchmark
        }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
                .measurement_time(Duration::from_secs(120))
                .sample_size(10);
            targets = public_params_benchmark
        }
    }
}

/// To run these benchmarks, first download `criterion` with `cargo install cargo install cargo-criterion`.
/// Then `cargo criterion --bench public_params`. The results are located in `target/criterion/data/<name-of-benchmark>`.
/// For flamegraphs, run `cargo criterion --bench public_params --features flamegraph -- --profile-time <secs>`.
/// The results are located in `target/criterion/profile/<name-of-benchmark>`.
criterion_main!(benches);
