use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::{Circuit, ConstraintSystem};
use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};
use pasta_curves::Fq;

use lurk::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{eval::evaluate, multiframe::MultiFrame, pointers::Ptr, store::Store},
    proof::{supernova::FoldingConfig, MultiFrameTrait},
    state::State,
};

fn fib<F: LurkField>(store: &Store<F>, state: Rc<RefCell<State>>, a: u64) -> Ptr {
    let program = format!(
        r#"
(let ((fib (lambda (target)
              (letrec ((next (lambda (a b target)
                               (if (= 0 target)
                                     a
                                     (next b
                                           (+ a b)
                                           (- target 1))))))
                (next 0 1 target)))))
  (fib {a}))
"#
    );

    store.read(state, &program).unwrap()
}

fn synthesize<M: measurement::Measurement>(
    name: &str,
    reduction_count: usize,
    c: &mut BenchmarkGroup<'_, M>,
) {
    let limit = 1_000_000;
    let lang_rc = Arc::new(Lang::<Fq, Coproc<Fq>>::new());
    let state = State::init_lurk_state().rccell();

    c.bench_with_input(
        BenchmarkId::new(name.to_string(), reduction_count),
        &reduction_count,
        |b, reduction_count| {
            let store = Store::default();
            let fib_n = (reduction_count / 3) as u64; // Heuristic, since one fib is 35 iterations.
            let ptr = fib::<pasta_curves::Fq>(&store, state.clone(), black_box(fib_n));
            let frames = evaluate::<Fq, Coproc<Fq>>(None, ptr, &store, limit).unwrap();

            let folding_config =
                Arc::new(FoldingConfig::new_ivc(lang_rc.clone(), *reduction_count));

            let multiframe =
                MultiFrame::from_frames(&frames, &store, folding_config.clone())[0].clone();

            b.iter_batched(
                || (multiframe.clone()), // avoid cloning the frames in the benchmark
                |multiframe| {
                    let mut cs = WitnessCS::new();
                    let result = multiframe.synthesize(&mut cs);
                    let _ = black_box(result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn fibonacci_synthesize(c: &mut Criterion) {
    let batch_sizes = [5, 10, 100, 200];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("synthesis");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);

    for size in batch_sizes.iter() {
        synthesize("Synthesis-rc", *size, &mut group);
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
            fibonacci_synthesize
        }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
            fibonacci_synthesize,
        }
    }
}

criterion_main!(benches);
