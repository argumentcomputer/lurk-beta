use anyhow::anyhow;
use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};
use pasta_curves::pallas;
use std::{sync::Arc, time::Duration};

use lurk::{
    eval::lang::{Coproc, Lang},
    lem::{eval::evaluate, store::Store},
    proof::nova::NovaProver,
    proof::Prover,
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
};

mod common;
use common::{
    fib::{fib_expr, fib_frame, fib_limit},
    set_bench_config,
};

use crate::common::fib::{test_coeffs, test_fib_io_matches};

#[derive(Clone, Debug, Copy)]
struct ProveParams {
    fib_n: usize,
    reduction_count: usize,
    date: &'static str,
    sha: &'static str,
}

impl ProveParams {
    fn name_params(&self) -> (String, String) {
        let output_type = bench_parameters_env().unwrap_or("stdout".into());
        match output_type.as_ref() {
            "pr-comment" => ("fib".into(), format!("num-{}", self.fib_n)),
            "commit-comment" => (
                format!("fib-ref={}", self.sha),
                format!("num-{}", self.fib_n),
            ),
            // TODO: refine "gh-pages",
            _ => (
                "fib".into(),
                format!("num-{}-{}-{}", self.fib_n, self.sha, self.date),
            ),
        }
    }
}

fn bench_parameters_env() -> anyhow::Result<String> {
    std::env::var("LURK_BENCH_OUTPUT")
        .map_err(|e| anyhow!("Noise threshold env var isn't set: {e}"))
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

fn fibonacci_prove<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
) {
    let limit = fib_limit(prove_params.fib_n, prove_params.reduction_count);
    let lang_pallas = Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new();
    let lang_rc = Arc::new(lang_pallas.clone());

    // use cached public params
    let instance = Instance::new(
        prove_params.reduction_count,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_params(&instance).unwrap();

    // Track the number of `Lurk frames / sec`
    let rc = prove_params.reduction_count as u64;
    c.throughput(criterion::Throughput::Elements(
        rc * u64::div_ceil(fib_frame(prove_params.fib_n) as u64, rc),
    ));
    let (name, params) = prove_params.name_params();

    c.bench_with_input(
        BenchmarkId::new(name, params),
        &prove_params,
        |b, prove_params| {
            let store = Store::default();

            let ptr = fib_expr::<pasta_curves::Fq>(&store);
            let prover = NovaProver::new(prove_params.reduction_count, lang_rc.clone());

            let frames =
                &evaluate::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>(None, ptr, &store, limit)
                    .unwrap();

            b.iter_batched(
                || frames,
                |frames| {
                    let result = prover.prove(&pp, frames, &store);
                    let _ = black_box(result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn fibonacci_benchmark(c: &mut Criterion) {
    // Running tests to make sure the constants are correct
    test_coeffs();
    test_fib_io_matches();

    // Uncomment to record the logs. May negatively impact performance
    //tracing_subscriber::fmt::init();
    set_bench_config();

    tracing::debug!("{:?}", lurk::config::LURK_CONFIG);

    let reduction_counts = rc_env().unwrap_or_else(|_| vec![100]);
    let batch_sizes = [100, 200];

    for reduction_count in reduction_counts.iter() {
        let mut group: BenchmarkGroup<'_, _> =
            c.benchmark_group(format!("LEM Fibonacci Prove - rc = {}", reduction_count));
        group.sampling_mode(SamplingMode::Flat); // This can take a *while*
        group.sample_size(10);
        group.noise_threshold(noise_threshold_env().unwrap_or(0.05));

        for fib_n in batch_sizes.iter() {
            let prove_params = ProveParams {
                fib_n: *fib_n,
                reduction_count: *reduction_count,
                date: env!("VERGEN_GIT_COMMIT_DATE"),
                sha: env!("VERGEN_GIT_SHA"),
            };
            fibonacci_prove(prove_params, &mut group);
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
             fibonacci_benchmark,
         }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
             fibonacci_benchmark,
         }
    }
}

criterion_main!(benches);
