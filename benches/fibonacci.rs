use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};

use lurk::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    proof::{
        nova::{NovaProver, Proof},
        Prover,
    },
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    state::State,
};
use pasta_curves::pallas;

mod common;
use common::set_bench_config;

#[allow(clippy::upper_case_acronyms)]
#[derive(Copy, Debug, Clone, PartialEq, Eq)]
enum Version {
    ALPHA,
    LEM,
}

#[derive(Clone, Debug, Copy)]
pub struct ProveParams {
    folding_steps: usize,
    reduction_count: usize,
    version: Version,
}

impl ProveParams {
    fn name(&self) -> String {
        format!("{:?},rc={}", self.version, self.reduction_count)
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
        prove_params: ProveParams,
        c: &mut BenchmarkGroup<'_, M>,
        state: &Rc<RefCell<State>>,
    ) {
        let ProveParams {
            folding_steps,
            reduction_count,
            version,
        } = prove_params;

        assert_eq!(version, Version::ALPHA);
        let limit = reduction_count * (folding_steps + 1);

        // Track the number of `folded iterations / sec`
        c.throughput(criterion::Throughput::Elements(
            (reduction_count * folding_steps) as u64,
        ));

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

        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        let parameter = format!("{},{},steps={}", date, sha, folding_steps);

        c.bench_with_input(
            BenchmarkId::new(prove_params.name(), parameter),
            &prove_params,
            |b, prove_params| {
                let store = Store::default();

                let env = empty_sym_env(&store);
                let ptr = fib::<pasta_curves::Fq>(&store, state.clone());
                let prover = NovaProver::new(prove_params.reduction_count, lang_pallas.clone());

                let frames = &prover
                    .get_evaluation_frames(ptr, env, &store, limit, lang_rc.clone())
                    .unwrap();

                // Here we split the proving step by first generating the recursive snark,
                // then have `criterion` only bench the rest of the folding steps
                let (recursive_snark, circuits, z0, _zi, _num_steps) = prover
                    .recursive_snark(&pp, frames, &store, &lang_rc)
                    .unwrap();

                b.iter_batched(
                    || (recursive_snark.clone(), z0.clone(), lang_rc.clone()),
                    |(recursive_snark, z0, lang_rc)| {
                        let result = Proof::prove_recursively(
                            &pp,
                            &store,
                            Some(recursive_snark),
                            &circuits,
                            reduction_count,
                            z0,
                            lang_rc,
                        );
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
        prove_params: ProveParams,
        c: &mut BenchmarkGroup<'_, M>,
        state: &Rc<RefCell<State>>,
    ) {
        let ProveParams {
            folding_steps,
            reduction_count,
            version,
        } = prove_params;

        assert_eq!(version, Version::LEM);
        let limit = reduction_count * (folding_steps + 1);

        // Track the number of `folded iterations / sec`
        c.throughput(criterion::Throughput::Elements(
            (reduction_count * folding_steps) as u64,
        ));

        let lang_pallas = Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new();
        let lang_rc = Arc::new(lang_pallas.clone());

        // use cached public params
        let instance: Instance<
            '_,
            pasta_curves::Fq,
            Coproc<pasta_curves::Fq>,
            MultiFrame<'_, pasta_curves::Fq, Coproc<pasta_curves::Fq>>,
        > = Instance::new(
            reduction_count,
            lang_rc.clone(),
            true,
            Kind::NovaPublicParams,
        );
        let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        let parameter = format!("{},{},steps={}", date, sha, folding_steps);

        c.bench_with_input(
            BenchmarkId::new(prove_params.name(), parameter),
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

                // Here we split the proving step by first generating the recursive snark,
                // then have `criterion` only bench the rest of the folding steps
                let (recursive_snark, circuits, z0, _zi, _num_steps) = prover
                    .recursive_snark(&pp, frames, &store, &lang_rc)
                    .unwrap();

                b.iter_batched(
                    || (recursive_snark.clone(), z0.clone(), lang_rc.clone()),
                    |(recursive_snark, z0, lang_rc)| {
                        let result = Proof::prove_recursively(
                            &pp,
                            &store,
                            Some(recursive_snark),
                            &circuits,
                            reduction_count,
                            z0,
                            lang_rc,
                        );
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
    let folding_step_sizes = [2, 4, 8];

    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("Fibonacci");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);

    let state = State::init_lurk_state().rccell();

    for folding_steps in folding_step_sizes.iter() {
        for reduction_count in reduction_counts.iter() {
            let alpha_params = ProveParams {
                folding_steps: *folding_steps,
                reduction_count: *reduction_count,
                version: Version::ALPHA,
            };
            alpha::prove(alpha_params, &mut group, &state);
        }
    }

    for folding_steps in folding_step_sizes.iter() {
        for reduction_count in reduction_counts.iter() {
            let lem_params = ProveParams {
                folding_steps: *folding_steps,
                reduction_count: *reduction_count,
                version: Version::LEM,
            };
            lem::prove(lem_params, &mut group, &state);
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
