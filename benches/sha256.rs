//! This benchmark measures the IVC performance of coprocessors, by adding a `sha256`
//! circuit alongside the lurk primary circuit. When supernova is integrated as a backend,
//! then NIVC performance can also be tested. This benchmark serves as a baseline for that
//! performance.
//!
//! Note: The example [example/sha256_ivc.rs] is this same benchmark but as an example
//! that's easier to play with and run.
use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};
use pasta_curves::pallas::Scalar as Fr;
use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use lurk::{
    circuit::circuit_frame::MultiFrame,
    coprocessor::sha256::{Sha256Coproc, Sha256Coprocessor},
    eval::{empty_sym_env, lang::Lang},
    field::LurkField,
    proof::{nova::NovaProver, supernova::SuperNovaProver, Prover},
    ptr::Ptr,
    public_parameters::{
        instance::{Instance, Kind},
        public_params, supernova_public_params,
    },
    state::{user_sym, State},
    store::Store,
};

mod common;
use common::set_bench_config;

fn sha256_ivc<F: LurkField>(
    store: &Store<F>,
    state: Rc<RefCell<State>>,
    arity: usize,
    n: usize,
    input: &[usize],
) -> Ptr<F> {
    assert_eq!(n, input.len());
    let input = input
        .iter()
        .map(|i| format!("(sha256 . {i})"))
        .collect::<Vec<String>>()
        .join(" ");
    let input = format!("'({input})");
    let program = format!(
        r#"
(letrec ((encode-1 (lambda (term) 
            (let ((type (car term))
                  (value (cdr term)))
                (if (eq 'sha256 type)
                    (eval (cons 'sha256_ivc_{arity} value))
                    (if (eq 'lurk type)
                        (commit value)
                        (if (eq 'id type)
                            value))))))
        (encode (lambda (input)
                (if input
                    (cons 
                        (encode-1 (car input))
                        (encode (cdr input)))))))
  (encode '((lurk . 5) (id . 15) {input})))
"#
    );

    store.read_with_state(state, &program).unwrap()
}

#[derive(Clone, Debug, Copy)]
struct ProveParams {
    arity: usize,
    n: usize,
    reduction_count: usize,
}

impl ProveParams {
    fn name(&self) -> String {
        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        format!(
            "{date}:{sha}:rc={}:sha256_ivc_{}",
            self.reduction_count, self.arity
        )
    }
}

fn sha256_ivc_prove<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
    state: &Rc<RefCell<State>>,
) {
    let ProveParams {
        arity,
        n: _,
        reduction_count,
    } = prove_params;

    let limit = 10000;

    let store = &mut Store::<Fr>::new();
    let cproc_sym = user_sym(&format!("sha256_ivc_{arity}"));

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(cproc_sym, Sha256Coprocessor::new(arity).into())],
    );
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance: Instance<
        '_,
        pasta_curves::Fq,
        Sha256Coproc<pasta_curves::Fq>,
        MultiFrame<'_, _, _>,
    > = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

    c.bench_with_input(
        BenchmarkId::new(prove_params.name(), arity),
        &prove_params,
        |b, prove_params| {
            let env = empty_sym_env(store);
            let ptr = sha256_ivc(
                store,
                state.clone(),
                black_box(prove_params.arity),
                black_box(prove_params.n),
                &(0..prove_params.n).collect::<Vec<_>>(),
            );

            let prover = NovaProver::new(prove_params.reduction_count, lang.clone());

            let frames = &prover
                .get_evaluation_frames(ptr, env, store, limit, lang_rc.clone())
                .unwrap();

            b.iter_batched(
                || (frames, lang_rc.clone()),
                |(frames, lang_rc)| {
                    let result = prover.prove(&pp, frames, store, &lang_rc);
                    let _ = black_box(result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn ivc_prove_benchmarks(c: &mut Criterion) {
    set_bench_config();
    tracing::debug!("{:?}", &lurk::config::LURK_CONFIG);
    let reduction_counts = [10, 100];
    let batch_sizes = [1, 2, 5, 10, 20];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("prove");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    let state = State::init_lurk_state().rccell();

    for &n in batch_sizes.iter() {
        for &reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                arity: 1,
                n,
                reduction_count,
            };
            sha256_ivc_prove(prove_params, &mut group, &state);
        }
    }
}

fn sha256_ivc_prove_compressed<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
    state: &Rc<RefCell<State>>,
) {
    let ProveParams {
        arity,
        n: _,
        reduction_count,
    } = prove_params;

    let limit = 10000;

    let store = &mut Store::<Fr>::new();
    let cproc_sym = user_sym(&format!("sha256_ivc_{arity}"));

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(cproc_sym, Sha256Coprocessor::new(arity).into())],
    );
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

    c.bench_with_input(
        BenchmarkId::new(prove_params.name(), arity),
        &prove_params,
        |b, prove_params| {
            let env = empty_sym_env(store);
            let ptr = sha256_ivc(
                store,
                state.clone(),
                black_box(prove_params.arity),
                black_box(prove_params.n),
                &(0..prove_params.n).collect::<Vec<_>>(),
            );

            let prover = NovaProver::new(prove_params.reduction_count, lang.clone());

            let frames = &prover
                .get_evaluation_frames(ptr, env, store, limit, lang_rc.clone())
                .unwrap();

            b.iter_batched(
                || (frames, lang_rc.clone()),
                |(frames, lang_rc)| {
                    let (proof, _, _, _) = prover.prove(&pp, frames, store, &lang_rc).unwrap();
                    let compressed_result = proof.compress(&pp).unwrap();

                    let _ = black_box(compressed_result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn ivc_prove_compressed_benchmarks(c: &mut Criterion) {
    set_bench_config();
    tracing::debug!("{:?}", &lurk::config::LURK_CONFIG);
    let reduction_counts = [10, 100];
    let batch_sizes = [1, 2, 5, 10, 20];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("prove_compressed");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    let state = State::init_lurk_state().rccell();

    for &n in batch_sizes.iter() {
        for &reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                arity: 1,
                n,
                reduction_count,
            };
            sha256_ivc_prove_compressed(prove_params, &mut group, &state);
        }
    }
}

fn sha256_nivc_prove<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
    state: &Rc<RefCell<State>>,
) {
    let ProveParams {
        arity,
        n: _,
        reduction_count,
    } = prove_params;

    let limit = 10000;

    let store = &mut Store::<Fr>::new();
    let cproc_sym = user_sym(&format!("sha256_ivc_{arity}"));

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(cproc_sym, Sha256Coprocessor::new(arity).into())],
    );
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        reduction_count,
        lang_rc.clone(),
        true,
        Kind::SuperNovaAuxParams,
    );
    let pp = supernova_public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

    c.bench_with_input(
        BenchmarkId::new(prove_params.name(), arity),
        &prove_params,
        |b, prove_params| {
            let env = empty_sym_env(store);
            let ptr = sha256_ivc(
                store,
                state.clone(),
                black_box(prove_params.arity),
                black_box(prove_params.n),
                &(0..prove_params.n).collect::<Vec<_>>(),
            );

            let prover = SuperNovaProver::new(prove_params.reduction_count, lang.clone());

            let frames = &prover
                .get_evaluation_frames(ptr, env, store, limit, lang_rc.clone())
                .unwrap();

            b.iter_batched(
                || (frames, lang_rc.clone()),
                |(frames, lang_rc)| {
                    let result = prover.prove(&pp, frames, store, lang_rc);
                    let _ = black_box(result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn nivc_prove_benchmarks(c: &mut Criterion) {
    set_bench_config();
    tracing::debug!("{:?}", &lurk::config::LURK_CONFIG);
    let reduction_counts = [10, 100];
    let batch_sizes = [1, 2, 5, 10, 20];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("prove");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    let state = State::init_lurk_state().rccell();

    for &n in batch_sizes.iter() {
        for &reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                arity: 1,
                n,
                reduction_count,
            };
            sha256_nivc_prove(prove_params, &mut group, &state);
        }
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "flamegraph")] {
        criterion_group! {
            name = ivc_benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10)
            .with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
            targets =
                ivc_prove_benchmarks,
                ivc_prove_compressed_benchmarks
         }
         criterion_group! {
            name = nivc_benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10)
            .with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
            targets =
                nivc_prove_benchmarks
                // TODO: Add when compressed SNARK is implemented for SuperNova
                // https://github.com/lurk-lab/arecibo/issues/27https://github.com/lurk-lab/arecibo/issues/27
                // nivc_prove_compressed_benchmarks
         }
    } else {
        criterion_group! {
            name = ivc_benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
                ivc_prove_benchmarks,
                ivc_prove_compressed_benchmarks
         }
         criterion_group! {
             name = nivc_benches;
             config = Criterion::default()
             .measurement_time(Duration::from_secs(120))
             .sample_size(10);
             targets =
                 nivc_prove_benchmarks
                 // TODO: Add when compressed SNARK is implemented for SuperNova
                 // https://github.com/lurk-lab/arecibo/issues/27https://github.com/lurk-lab/arecibo/issues/27
                 // nivc_prove_compressed_benchmarks
          }
    }
}

criterion_main!(ivc_benches, nivc_benches);
