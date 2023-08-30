use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use camino::Utf8Path;
use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};

use pasta_curves::pallas;

use lurk::{
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
    },
    field::LurkField,
    proof::nova::NovaProver,
    proof::Prover,
    ptr::Ptr,
    public_parameters::public_params,
    state::State,
    store::Store,
};

const PUBLIC_PARAMS_PATH: &str = "/var/tmp/lurk_benches/public_params";
fn fib<F: LurkField>(store: &mut Store<F>, state: Rc<RefCell<State>>, _a: u64) -> Ptr<F> {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

    store.read_with_state(state, program).unwrap()
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

struct ProveParams {
    fib_n: usize,
    reduction_count: usize,
}

impl ProveParams {
    fn name(&self) -> String {
        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        format!("{date}:{sha}:Fibonacci-rc={}", self.reduction_count)
    }
}

fn fibo_prove<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
    state: Rc<RefCell<State>>,
) {
    let ProveParams {
        fib_n,
        reduction_count,
    } = prove_params;

    let limit = fib_limit(fib_n, reduction_count);
    let lang_pallas = Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new();
    let lang_rc = Arc::new(lang_pallas.clone());

    // use cached public params
    let pp = public_params(
        prove_params.reduction_count,
        true,
        lang_rc.clone(),
        Utf8Path::new(PUBLIC_PARAMS_PATH),
    )
    .unwrap();

    c.bench_with_input(
        BenchmarkId::new(prove_params.name(), fib_n),
        &prove_params,
        |b, _prove_params| {
            let mut store = Store::default();

            let env = empty_sym_env(&store);
            let ptr = fib::<pasta_curves::Fq>(&mut store, state.clone(), black_box(fib_n as u64));
            let prover = NovaProver::new(reduction_count, lang_pallas.clone());

            let frames = &prover
                .get_evaluation_frames(ptr, env, &mut store, limit, &lang_pallas)
                .unwrap();

            b.iter_batched(
                || (frames, lang_rc.clone()),
                |(frames, lang_rc)| {
                    let result = prover.prove(&pp, frames, &mut store, &lang_rc);
                    let _ = black_box(result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn fibonacci_prove(c: &mut Criterion) {
    let _ = dbg!(&*lurk::config::CONFIG);
    let reduction_counts = vec![100, 600, 700, 800, 900];
    let batch_sizes = vec![100, 200];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("Prove");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    let state = State::init_lurk_state().rccell();

    for fib_n in batch_sizes.iter() {
        for reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                fib_n: *fib_n,
                reduction_count: *reduction_count,
            };
            fibo_prove(prove_params, &mut group, state.clone());
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
