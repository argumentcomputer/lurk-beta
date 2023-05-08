use blstrs::Scalar as Fr;
use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, SamplingMode,
};
use lurk::{
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
        Evaluator,
    },
    field::LurkField,
    proof::nova::NovaProver,
    proof::Prover,
    ptr::Ptr,
    public_parameters,
    store::Store,
};
use std::sync::Arc;
use std::time::Duration;

const DEFAULT_REDUCTION_COUNT: usize = 10;
fn go_base<F: LurkField>(store: &mut Store<F>, a: u64, b: u64) -> Ptr<F> {
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

    store.read(&program).unwrap()
}

fn end2end_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("end2end_benchmark");
    group
        .sampling_mode(SamplingMode::Flat)
        .measurement_time(Duration::from_secs(120))
        .sample_size(10);

    let limit = 1_000_000_000;
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();
    let lang_vesta_rc = Arc::new(lang_vesta.clone());
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    // setup
    let mut store = Store::default();
    let env = empty_sym_env(&store);
    let prover = NovaProver::new(reduction_count, lang_vesta);

    // use cached public params
    let pp = public_parameters::public_params(reduction_count, lang_vesta_rc.clone()).unwrap();

    let size = (10, 0);
    let benchmark_id = BenchmarkId::new("end2end_go_base_nova", format!("_{}_{}", size.0, size.1));

    group.bench_with_input(benchmark_id, &size, |b, &s| {
        b.iter(|| {
            let ptr = go_base::<pasta_curves::Fq>(&mut store, s.0, s.1);
            let _result = prover
                .evaluate_and_prove(&pp, ptr, env, &mut store, limit, lang_vesta_rc.clone())
                .unwrap();
        })
    });

    group.finish();
}

fn store_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("store_benchmark");
    group
        .measurement_time(Duration::from_secs(5))
        .sample_size(60);

    let mut bls12_store = Store::<Fr>::default();
    let mut pallas_store = Store::<pasta_curves::Fp>::default();

    // todo!() rfc out into more flexible test cases
    let sizes = vec![(10, 16), (10, 160)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);

        let bls12_id = BenchmarkId::new("store_go_base_bls12", &parameter_string);
        group.bench_with_input(bls12_id, &size, |b, &s| {
            b.iter(|| {
                let result = go_base::<Fr>(&mut bls12_store, s.0, s.1);
                black_box(result)
            })
        });

        let pasta_id = BenchmarkId::new("store_go_base_pallas", &parameter_string);
        group.bench_with_input(pasta_id, &size, |b, &s| {
            b.iter(|| {
                let result = go_base::<pasta_curves::Fp>(&mut pallas_store, s.0, s.1);
                black_box(result)
            })
        });
    }

    group.finish();
}

fn hydration_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("hydration_benchmark");
    group
        .measurement_time(Duration::from_secs(5))
        .sample_size(60);

    let mut bls12_store = Store::<Fr>::default();
    let mut pallas_store = Store::<pasta_curves::Fp>::default();

    // todo!() rfc out into more flexible test cases
    let sizes = vec![(10, 16), (10, 160)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);

        {
            let benchmark_id = BenchmarkId::new("hydration_go_base_bls12", &parameter_string);
            group.bench_with_input(benchmark_id, &size, |b, &s| {
                let _ptr = go_base::<Fr>(&mut bls12_store, s.0, s.1);
                b.iter(|| bls12_store.hydrate_scalar_cache())
            });
        }

        {
            let benchmark_id = BenchmarkId::new("hydration_go_base_pallas", &parameter_string);
            group.bench_with_input(benchmark_id, &size, |b, &s| {
                let _ptr = go_base::<pasta_curves::Fp>(&mut pallas_store, s.0, s.1);
                b.iter(|| pallas_store.hydrate_scalar_cache())
            });
        }
    }

    group.finish();
}

fn eval_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("eval_benchmark");
    group
        .measurement_time(Duration::from_secs(5))
        .sample_size(60);

    let limit = 1_000_000_000;
    let lang_bls12 = Lang::<Fr, Coproc<Fr>>::new();
    let lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();
    let mut bls12_store = Store::<Fr>::default();
    let mut pallas_store = Store::<pasta_curves::Fp>::default();

    // todo!() rfc out into more flexible test cases
    let sizes = vec![(10, 16), (10, 160)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);

        {
            let benchmark_id = BenchmarkId::new("eval_go_base_bls12", &parameter_string);
            group.bench_with_input(benchmark_id, &size, |b, &s| {
                let ptr = go_base::<Fr>(&mut bls12_store, s.0, s.1);
                b.iter(|| {
                    Evaluator::new(
                        ptr,
                        empty_sym_env(&bls12_store),
                        &mut bls12_store,
                        limit,
                        &lang_bls12,
                    )
                    .eval()
                })
            });
        }

        {
            let benchmark_id = BenchmarkId::new("eval_go_base_pallas", &parameter_string);
            group.bench_with_input(benchmark_id, &size, |b, &s| {
                let ptr = go_base::<pasta_curves::Fp>(&mut pallas_store, s.0, s.1);
                b.iter(|| {
                    Evaluator::new(
                        ptr,
                        empty_sym_env(&pallas_store),
                        &mut pallas_store,
                        limit,
                        &lang_pallas,
                    )
                    .eval()
                })
            });
        }
    }

    group.finish();
}

// todo!(): come back to this later when we know what to do with circuit generation
// fn circuit_generation_benchmark(c: &mut Criterion) {
//     let mut group = c.benchmark_group("eval_benchmark");
//     group.measurement_time(Duration::from_secs(5))
//          .sample_size(60);

//     let limit = 1_000_000_000;
//     let _lang_bls = Lang::<Fr, Coproc<Fr>>::new();
//     let _lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();
//     let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();

//     let reduction_count = DEFAULT_REDUCTION_COUNT;

//     group.bench_function("circuit_generation_go_base_10_16_nova", |b| {
//         let mut store = Store::default();
//         let env = empty_sym_env(&store);
//         let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(16));
//         let prover = NovaProver::new(reduction_count, lang_vesta.clone());

//         let pp = public_parameters::public_params(reduction_count).unwrap();
//         let frames = prover
//             .get_evaluation_frames(ptr, env, &mut store, limit, &lang_vesta)
//             .unwrap();

//         b.iter(|| {
//             let result = prover
//                 .prove(&pp, frames.clone(), &mut store, &lang_vesta)
//                 .unwrap();
//             black_box(result);
//         })
//     });
// }

fn prove_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("prove_benchmark");
    group
        .sampling_mode(SamplingMode::Flat)
        .measurement_time(Duration::from_secs(120))
        .sample_size(10);

    let limit = 1_000_000_000;
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();
    let lang_vesta_rc = Arc::new(lang_vesta.clone());
    let mut store = Store::default();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let size = (10, 0);
    let benchmark_id = BenchmarkId::new("prove_go_base_nova", format!("_{}_{}", size.0, size.1));

    group.bench_with_input(benchmark_id, &size, |b, &s| {
        let ptr = go_base::<pasta_curves::Fq>(&mut store, s.0, s.1);
        let prover = NovaProver::new(reduction_count, lang_vesta.clone());
        let pp = public_parameters::public_params(reduction_count, lang_vesta_rc.clone()).unwrap();
        let frames = prover
            .get_evaluation_frames(ptr, empty_sym_env(&store), &mut store, limit, &lang_vesta)
            .unwrap();

        b.iter(|| {
            let result = prover
                .prove(&pp, frames.clone(), &mut store, lang_vesta_rc.clone())
                .unwrap();
            black_box(result);
        })
    });
}

fn verify_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_benchmark");
    group
        .measurement_time(Duration::from_secs(10))
        .sample_size(10);

    let limit = 1_000_000_000;
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();
    let lang_vesta_rc = Arc::new(lang_vesta.clone());
    let mut store = Store::default();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let sizes = vec![(10, 0)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);
        let benchmark_id = BenchmarkId::new("verify_go_base_nova", &parameter_string);
        group.bench_with_input(benchmark_id, &size, |b, &s| {
            let ptr = go_base(&mut store, s.0, s.1);
            let prover = NovaProver::new(reduction_count, lang_vesta.clone());
            let pp =
                public_parameters::public_params(reduction_count, lang_vesta_rc.clone()).unwrap();
            let frames = prover
                .get_evaluation_frames(ptr, empty_sym_env(&store), &mut store, limit, &lang_vesta)
                .unwrap();
            let (proof, z0, zi, num_steps) = prover
                .prove(&pp, frames, &mut store, lang_vesta_rc.clone())
                .unwrap();

            b.iter_batched(
                || z0.clone(),
                |z0| {
                    let result = proof.verify(&pp, num_steps, z0, &zi[..]).unwrap();
                    black_box(result);
                },
                BatchSize::LargeInput,
            )
        });
    }

    group.finish();
}

fn verify_compressed_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_compressed_benchmark");
    group
        .measurement_time(Duration::from_secs(10))
        .sample_size(10);

    let limit = 1_000_000_000;
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();
    let lang_vesta_rc = Arc::new(lang_vesta.clone());
    let mut store = Store::default();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    let sizes = vec![(10, 0)];
    for size in sizes {
        let parameter_string = format!("_{}_{}", size.0, size.1);
        let benchmark_id = BenchmarkId::new("verify_compressed_go_base_nova", &parameter_string);
        group.bench_with_input(benchmark_id, &size, |b, &s| {
            let ptr = go_base(&mut store, s.0, s.1);
            let prover = NovaProver::new(reduction_count, lang_vesta.clone());
            let pp =
                public_parameters::public_params(reduction_count, lang_vesta_rc.clone()).unwrap();
            let frames = prover
                .get_evaluation_frames(ptr, empty_sym_env(&store), &mut store, limit, &lang_vesta)
                .unwrap();
            let (proof, z0, zi, num_steps) = prover
                .prove(&pp, frames, &mut store, lang_vesta_rc.clone())
                .unwrap();

            let compressed_proof = proof.compress(&pp).unwrap();

            b.iter_batched(
                || z0.clone(),
                |z0| {
                    let result = compressed_proof
                        .verify(&pp, num_steps, z0, &zi[..])
                        .unwrap();
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
        criterion_group! {
            name = benches;
            config = Criterion::default()
                .with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
            targets =
                end2end_benchmark,
                store_benchmark,
                hydration_benchmark,
                eval_benchmark,
                // circuit_generation_benchmark,
                prove_benchmark,
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
                // circuit_generation_benchmark,
                prove_benchmark,
                verify_benchmark,
                verify_compressed_benchmark
        }
    }
}

criterion_main!(benches);
