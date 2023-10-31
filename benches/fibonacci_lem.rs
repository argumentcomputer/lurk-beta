use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use anyhow::anyhow;
use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};

use pasta_curves::pallas;

use lurk::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{eval::evaluate, multiframe::MultiFrame, pointers::Ptr, store::Store},
    proof::nova::NovaProver,
    proof::Prover,
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    state::State,
};

mod common;
use common::set_bench_config;

fn fib<F: LurkField>(store: &Store<F>, state: Rc<RefCell<State>>, _a: u64) -> Ptr<F> {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

    store.read(state, program).unwrap()
}

// The env output in the `fib_frame`th frame of the above, infinite Fibonacci computation will contain a binding of the
// nth Fibonacci number to `a`.
// means of computing it.]
fn fib_frame(n: usize) -> usize {
    11 + 16 * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}

#[derive(Clone, Debug, Copy)]
struct ProveParams {
    fib_n: usize,
    reduction_count: usize,
}

impl ProveParams {
    fn name(&self) -> String {
        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        format!("{date}:{sha}:Fibonacci-LEM-rc={}", self.reduction_count)
    }
}

fn fibo_prove<M: measurement::Measurement>(
    prove_params: ProveParams,
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
        BenchmarkId::new(prove_params.name(), fib_n),
        &prove_params,
        |b, prove_params| {
            let store = Store::default();

            let ptr = fib::<pasta_curves::Fq>(
                &store,
                state.clone(),
                black_box(prove_params.fib_n as u64),
            );
            let prover = NovaProver::new(prove_params.reduction_count, lang_pallas.clone());

            let frames =
                &evaluate::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>(None, ptr, &store, limit)
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

fn rc_env() -> anyhow::Result<Vec<usize>> {
    std::env::var("LURK_RC")
        .map_err(|e| anyhow!("Reduction count env var isn't set: {e}"))
        .and_then(|rc| {
            let vec: anyhow::Result<Vec<usize>> = rc
                .split(',')
                .map(|rc| {
                    rc.parse::<usize>()
                        .map_err(|e| anyhow!("Failed to parse RC: {e}"))
                })
                .collect();
            vec
        })
}

fn noise_threshold_env() -> anyhow::Result<f64> {
    std::env::var("LURK_BENCH_NOISE_THRESHOLD")
        .map_err(|e| anyhow!("Noise threshold env var isn't set: {e}"))
        .and_then(|nt| {
            nt.parse::<f64>()
                .map_err(|e| anyhow!("Failed to parse noise threshold: {e}"))
        })
}

fn fibonacci_prove(c: &mut Criterion) {
    tracing_subscriber::fmt::init();
    set_bench_config();
    tracing::debug!("{:?}", lurk::config::LURK_CONFIG);

    let reduction_counts = rc_env().unwrap_or_else(|_| vec![100]);
    let batch_sizes = [100, 200];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("Prove");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    group.noise_threshold(noise_threshold_env().unwrap_or(0.05));

    let state = State::init_lurk_state().rccell();

    for fib_n in batch_sizes.iter() {
        for reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                fib_n: *fib_n,
                reduction_count: *reduction_count,
            };
            fibo_prove(prove_params, &mut group, &state);
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
             fibonacci_prove,
         }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
             fibonacci_prove,
         }
    }
}

criterion_main!(benches);
