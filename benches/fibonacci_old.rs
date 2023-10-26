use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};

use lurk::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    proof::{nova::NovaProver, Prover},
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    state::State,
};
use pasta_curves::pallas;

mod common;
use common::set_bench_config;

fn fib_frame(n: usize) -> usize {
    11 + 16 * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}

pub struct ProveParams {
    fib_n: usize,
    reduction_count: usize,
}

impl ProveParams {
    fn name(&self, lem: bool) -> String {
        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        let lem = if lem { "-LEM" } else { "" };
        format!("{date}:{sha}:Fibonacci{lem}-rc={}", self.reduction_count)
    }
}

mod alpha {
    use lurk::{circuit::circuit_frame::MultiFrame, eval::empty_sym_env, ptr::Ptr, store::Store};

    use super::*;

    fn fib<F: LurkField>(store: &Store<F>, state: Rc<RefCell<State>>) -> Ptr<F> {
        let program = r#"
    (letrec ((next (lambda (a b) (next b (+ a b))))
               (fib (next 0 1)))
      (fib))
    "#;

        store.read_with_state(state, program).unwrap()
    }

    pub fn prove<M: measurement::Measurement>(
        prove_params: &ProveParams,
        c: &mut BenchmarkGroup<'_, M>,
        state: &Rc<RefCell<State>>,
    ) {
        let ProveParams {
            fib_n,
            reduction_count,
        } = prove_params;

        let limit = fib_limit(fib_n, reduction_count);
        let lang_pallas = Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new();
        let lang_rc = Arc::new(lang_pallas.clone());

        // use cached public params
        let instance = Instance::new(
            reduction_count,
            lang_rc.clone(),
            true,
            Kind::NovaPublicParams,
        );
        let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

        c.bench_with_input(
            BenchmarkId::new(prove_params.name(false), fib_n),
            &prove_params,
            |b, prove_params| {
                let store = Store::default();

                let env = empty_sym_env(&store);
                let ptr = fib::<pasta_curves::Fq>(&store, state.clone());
                let prover = NovaProver::new(prove_params.reduction_count, lang_pallas.clone());

                let frames = &prover
                    .get_evaluation_frames(ptr, env, &store, limit, lang_rc.clone())
                    .unwrap();

                b.iter_batched(
                    || (frames, lang_rc.clone()),
                    |(frames, lang_rc)| {
                        let result = prover.prove(&pp, frames, &store, &lang_rc);
                        let _ = black_box(result);
                    },
                    BatchSize::LargeInput,
                )
            },
        );
    }
}

mod lem {
    use lurk::lem::{eval::evaluate, multiframe::MultiFrame, pointers::Ptr, store::Store};

    use super::*;

    fn fib<F: LurkField>(store: &Store<F>, state: Rc<RefCell<State>>) -> Ptr<F> {
        let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

        store.read(state, program).unwrap()
    }

    pub fn prove<M: measurement::Measurement>(
        prove_params: &ProveParams,
        c: &mut BenchmarkGroup<'_, M>,
        state: &Rc<RefCell<State>>,
    ) {
        let ProveParams {
            fib_n,
            reduction_count,
        } = prove_params;

        let limit = fib_limit(fib_n, reduction_count);
        let lang_pallas = Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new();
        let lang_rc = Arc::new(lang_pallas.clone());

        // use cached public params
        let instance = Instance::new(
            reduction_count,
            lang_rc.clone(),
            true,
            Kind::NovaPublicParams,
        );
        let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

        c.bench_with_input(
            BenchmarkId::new(prove_params.name(true), fib_n),
            &prove_params,
            |b, prove_params| {
                let store = Store::default();

                let ptr = fib::<pasta_curves::Fq>(&store, state.clone());
                let prover = NovaProver::new(prove_params.reduction_count, lang_pallas.clone());

                let frames = &evaluate::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>(
                    None, ptr, &store, limit,
                )
                .unwrap()
                .0;

                b.iter_batched(
                    || (frames, lang_rc.clone()),
                    |(frames, lang_rc)| {
                        let result = prover.prove(&pp, frames, &store, &lang_rc);
                        let _ = black_box(result);
                    },
                    BatchSize::LargeInput,
                )
            },
        );
    }
}

fn fib_bench(c: &mut Criterion) {
    set_bench_config();
    tracing::debug!("{:?}", lurk::config::LURK_CONFIG);
    let reduction_counts = [100, 600, 700, 800, 900];
    let batch_sizes = [100, 200];

    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("Fibonacci");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);

    let state = State::init_lurk_state().rccell();

    for fib_n in batch_sizes.iter() {
        for reduction_count in reduction_counts.iter() {
            let params = ProveParams {
                fib_n: *fib_n,
                reduction_count: *reduction_count,
            };
            alpha::prove(&params, &mut group, &state);
            lem::prove(&params, &mut group, &state);
        }
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "flamegraph")] {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10)
            .with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
            targets =
                fib_bench,
         }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
                fib_bench,
         }
    }
}

criterion_main!(benches);
