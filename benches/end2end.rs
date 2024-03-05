use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, SamplingMode,
};
use halo2curves::bn256::Fr as Bn;
use std::{sync::Arc, time::Duration};

use lurk::{
    field::LurkField,
    lang::{Coproc, Lang},
    lem::{
        eval::{evaluate, evaluate_simple},
        pointers::Ptr,
        store::Store,
    },
    proof::{nova::NovaProver, RecursiveSNARKTrait},
    public_parameters::{
        self,
        instance::{Instance, Kind},
    },
    state::{State, StateRcCell},
};

mod common;
use common::set_bench_config;

const DEFAULT_REDUCTION_COUNT: usize = 10;

fn go_base<F: LurkField>(store: &Store<F>, state: StateRcCell, a: u64, b: u64) -> Ptr {
    let program = format!(
        r#"
(let ((foo (lambda (a b)
              (letrec ((aux (lambda (i a x)
                               (if (= i b)
                                     x
                                     (let ((x (+ x a))
                                            (a (+ a (* b 2))))
                                       (aux (+ i 1) a x))))))
                       (let ((x (+ (* a b) 4)))
                         (aux 0 a x))))))
  (foo {a} {b}))
"#
    );

    store.read(state, &program).unwrap()
}

/// To run these benchmarks, do `cargo criterion end2end_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion end2end_benchmark --features flamegraph -- --profile-time <secs>```
fn end2end_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("end2end_benchmark");
    group
        .sampling_mode(SamplingMode::Flat)
        .measurement_time(Duration::from_secs(120))
        .sample_size(10);

    set_bench_config();
    let limit = 1_000_000_000;
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    // setup
    let lang = Lang::<Bn>::new();
    let lang_rc = Arc::new(lang.clone());

    let store = Store::default();
    let prover: NovaProver<'_, Bn, Coproc<Bn>> = NovaProver::new(reduction_count, lang_rc.clone());

    // use cached public params
    let instance = Instance::new(reduction_count, lang_rc, true, Kind::NovaPublicParams);
    let pp = public_parameters::public_params(&instance).unwrap();

    let size = (10, 0);
    let benchmark_id = BenchmarkId::new("end2end_go_base_nova", format!("_{}_{}", size.0, size.1));

    let state = State::init_lurk_state().rccell();

    group.bench_with_input(benchmark_id, &size, |b, &s| {
        b.iter(|| {
            let ptr = go_base::<Bn>(&store, state.clone(), s.0, s.1);
            let frames = evaluate::<Bn, Coproc<Bn>>(None, ptr, &store, limit).unwrap();
            let _result = prover.prove_from_frames(&pp, &frames, &store).unwrap();
        })
    });

    group.finish();
}

/// To run these benchmarks, do `cargo criterion store_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion store_benchmark --features flamegraph -- --profile-time <secs>```
fn store_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("store_benchmark");
    group
        .measurement_time(Duration::from_secs(5))
        .sample_size(60);

    let store = Store::<Bn>::default();

    let state = State::init_lurk_state().rccell();

    // todo!() rfc out into more flexible test cases
    let sizes = [(10, 16), (10, 160)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);

        let pasta_id = BenchmarkId::new("store_go_base", &parameter_string);
        group.bench_with_input(pasta_id, &size, |b, &s| {
            b.iter(|| {
                let result = go_base::<Bn>(&store, state.clone(), s.0, s.1);
                black_box(result)
            })
        });
    }

    group.finish();
}

/// To run these benchmarks, do `cargo criterion hydration_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion hydration_benchmark --features flamegraph -- --profile-time <secs>```
fn hydration_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("hydration_benchmark");
    group
        .measurement_time(Duration::from_secs(5))
        .sample_size(60);

    let store = Store::<Bn>::default();

    let state = State::init_lurk_state().rccell();

    // todo!() rfc out into more flexible test cases
    let sizes = [(10, 16), (10, 160)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);

        {
            let benchmark_id = BenchmarkId::new("hydration_go_base", &parameter_string);
            group.bench_with_input(benchmark_id, &size, |b, &s| {
                let _ptr = go_base::<Bn>(&store, state.clone(), s.0, s.1);
                b.iter(|| store.hydrate_z_cache())
            });
        }
    }

    group.finish();
}

/// To run these benchmarks, do `cargo criterion eval_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion eval_benchmark --features flamegraph -- --profile-time <secs>```
fn eval_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("eval_benchmark");
    group
        .measurement_time(Duration::from_secs(5))
        .sample_size(60);

    let limit = 1_000_000_000;
    let store = Store::default();

    let state = State::init_lurk_state().rccell();

    // todo!() rfc out into more flexible test cases
    let sizes = [(10, 16), (10, 160)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);
        {
            let benchmark_id = BenchmarkId::new("eval_go_base", &parameter_string);
            group.bench_with_input(benchmark_id, &size, |b, &s| {
                let ptr = go_base::<Bn>(&store, state.clone(), s.0, s.1);
                b.iter(|| evaluate_simple::<Bn, Coproc<Bn>>(None, ptr, &store, limit))
            });
        }
    }

    group.finish();
}

/// To run these benchmarks, do `cargo criterion prove_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion prove_benchmark --features flamegraph -- --profile-time <secs>```
fn prove_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("prove_benchmark");
    group
        .sampling_mode(SamplingMode::Flat)
        .measurement_time(Duration::from_secs(120))
        .sample_size(10);

    set_bench_config();
    let limit = 1_000_000_000;
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let store = Store::default();

    let size = (10, 0);
    let benchmark_id = BenchmarkId::new("prove_go_base_nova", format!("_{}_{}", size.0, size.1));

    let state = State::init_lurk_state().rccell();

    let lang = Lang::<Bn>::new();
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_parameters::public_params(&instance).unwrap();

    group.bench_with_input(benchmark_id, &size, |b, &s| {
        let ptr = go_base::<Bn>(&store, state.clone(), s.0, s.1);
        let prover: NovaProver<'_, Bn, Coproc<Bn>> =
            NovaProver::new(reduction_count, lang_rc.clone());
        let frames = evaluate::<Bn, Coproc<Bn>>(None, ptr, &store, limit).unwrap();

        b.iter(|| {
            let result = prover.prove_from_frames(&pp, &frames, &store).unwrap();
            black_box(result);
        })
    });
}

/// To run these benchmarks, do `cargo criterion prove_compressed_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion prove_compressed_benchmark --features flamegraph -- --profile-time <secs>```
fn prove_compressed_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("prove_compressed_benchmark");
    group
        .sampling_mode(SamplingMode::Flat)
        .measurement_time(Duration::from_secs(120))
        .sample_size(10);

    set_bench_config();
    let limit = 1_000_000_000;
    let store = Store::default();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let size = (10, 0);
    let benchmark_id = BenchmarkId::new(
        "prove_compressed_go_base_nova",
        format!("_{}_{}", size.0, size.1),
    );

    let state = State::init_lurk_state().rccell();

    let lang = Lang::<Bn>::new();
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_parameters::public_params(&instance).unwrap();

    group.bench_with_input(benchmark_id, &size, |b, &s| {
        let ptr = go_base::<Bn>(&store, state.clone(), s.0, s.1);
        let prover = NovaProver::new(reduction_count, lang_rc.clone());
        let frames = evaluate::<Bn, Coproc<Bn>>(None, ptr, &store, limit).unwrap();

        b.iter(|| {
            let (proof, _, _, _) = prover.prove_from_frames(&pp, &frames, &store).unwrap();

            let compressed_result = proof.compress(&pp).unwrap();
            black_box(compressed_result);
        })
    });
}

/// To run these benchmarks, do `cargo criterion verify_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion verify_benchmark --features flamegraph -- --profile-time <secs>```
fn verify_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_benchmark");
    group
        .measurement_time(Duration::from_secs(10))
        .sample_size(10);

    set_bench_config();
    let limit = 1_000_000_000;
    let store = Store::default();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let state = State::init_lurk_state().rccell();

    let lang = Lang::<Bn>::new();
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_parameters::public_params(&instance).unwrap();

    let sizes = [(10, 0)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);
        let benchmark_id = BenchmarkId::new("verify_go_base_nova", &parameter_string);
        group.bench_with_input(benchmark_id, &size, |b, &s| {
            let ptr = go_base(&store, state.clone(), s.0, s.1);
            let prover = NovaProver::new(reduction_count, lang_rc.clone());
            let frames = evaluate::<Bn, Coproc<Bn>>(None, ptr, &store, limit).unwrap();
            let (proof, z0, zi, _num_steps) =
                prover.prove_from_frames(&pp, &frames, &store).unwrap();

            b.iter_batched(
                || z0.clone(),
                |z0| {
                    let result = proof.verify(&pp, &z0, &zi[..]).unwrap();
                    black_box(result);
                },
                BatchSize::LargeInput,
            )
        });
    }

    group.finish();
}

/// To run these benchmarks, do `cargo criterion verify_compressed_benchmark`.
/// For flamegraphs, run:
/// ```cargo criterion verify_compressed_benchmark --features flamegraph -- --profile-time <secs>```
fn verify_compressed_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_compressed_benchmark");
    group
        .measurement_time(Duration::from_secs(10))
        .sample_size(10);

    set_bench_config();
    let limit = 1_000_000_000;
    let store = Store::default();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let state = State::init_lurk_state().rccell();

    let lang = Lang::<Bn>::new();
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_parameters::public_params(&instance).unwrap();

    let sizes = [(10, 0)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);
        let benchmark_id = BenchmarkId::new("verify_compressed_go_base_nova", &parameter_string);
        group.bench_with_input(benchmark_id, &size, |b, &s| {
            let ptr = go_base(&store, state.clone(), s.0, s.1);
            let prover = NovaProver::new(reduction_count, lang_rc.clone());
            let frames = evaluate::<Bn, Coproc<Bn>>(None, ptr, &store, limit).unwrap();
            let (proof, z0, zi, _num_steps) =
                prover.prove_from_frames(&pp, &frames, &store).unwrap();

            let compressed_proof = proof.compress(&pp).unwrap();

            b.iter_batched(
                || z0.clone(),
                |z0| {
                    let result = compressed_proof.verify(&pp, &z0, &zi[..]).unwrap();
                    black_box(result);
                },
                BatchSize::LargeInput,
            )
        });
    }

    group.finish();
}

cfg_if::cfg_if! {

    if #[cfg(feature = "flamegraph")] {
        // In order to collect a flamegraph, you need to indicate a profile time, see
        // https://github.com/tikv/pprof-rs#integrate-with-criterion
        // Example usage :
        // cargo criterion --bench fibonacci --features flamegraph -- --profile-time 5
        // Warning: it is not recommended to run this on an M1 Mac, as making pprof work well there is hard.
        criterion_group! {
            name = benches;
            config = Criterion::default()
                .with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
            targets =
                end2end_benchmark,
                store_benchmark,
                hydration_benchmark,
                eval_benchmark,
                prove_benchmark,
                prove_compressed_benchmark,
                verify_benchmark,
                verify_compressed_benchmark
        }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default();
            targets =
                end2end_benchmark,
                store_benchmark,
                hydration_benchmark,
                eval_benchmark,
                prove_benchmark,
                prove_compressed_benchmark,
                verify_benchmark,
                verify_compressed_benchmark
        }
    }
}

// To run these benchmarks, first download `criterion` with `cargo install cargo-criterion`.
// Then `cargo criterion --bench end2end_lem`. The results are located in `target/criterion/data/<name-of-benchmark>`.
// For flamegraphs, run `cargo criterion --bench end2end_lem --features flamegraph -- --profile-time <secs>`.
// The results are located in `target/criterion/profile/<name-of-benchmark>`.
criterion_main!(benches);
