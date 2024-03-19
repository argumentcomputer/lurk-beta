use criterion::{
    black_box, criterion_group, criterion_main, measurement, BenchmarkGroup, BenchmarkId,
    Criterion, SamplingMode,
};
use halo2curves::bn256::Fr;
use std::{sync::Arc, time::Duration};

use lurk::{
    coprocessor::trie::{install, TrieCoproc},
    dual_channel::dummy_terminal,
    lang::Lang,
    lem::{
        eval::{evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig},
        interpreter::Frame,
        store::Store,
    },
    proof::supernova::{public_params, SuperNovaProver},
    state::State,
};

const CODE: &str = "
(let ((fib (letrec ((next (lambda (a b n target)
               (if (eq n target)
                   a
                   (next b
                         (+ a b)
                         (+ 1 n)
                         target))))
            (fib (next 0 1 0)))
          fib))
      (fib-trie (.lurk.trie.new))
      (fib-trie (.lurk.trie.insert fib-trie 40 (fib 40)))
      (fib-trie (.lurk.trie.insert fib-trie 50 (fib 50))))
  (+ (num (.lurk.trie.lookup fib-trie 40)) (num (.lurk.trie.lookup fib-trie 50))))";

fn prove<M: measurement::Measurement>(
    name: &str,
    reduction_count: usize,
    lang: &Arc<Lang<Fr, TrieCoproc<Fr>>>,
    store: &Store<Fr>,
    frames: &[Frame],
    c: &mut BenchmarkGroup<'_, M>,
) {
    c.bench_with_input(
        BenchmarkId::new(name.to_string(), reduction_count),
        &reduction_count,
        |b, reduction_count| {
            let rc = *reduction_count;
            let prover = SuperNovaProver::new(rc, lang.clone());
            let pp = public_params(rc, lang.clone());
            b.iter(|| {
                let (proof, ..) = prover.prove_from_frames(&pp, frames, store, None).unwrap();
                let _ = black_box(proof);
            })
        },
    );
}

fn trie_nivc(c: &mut Criterion) {
    let batch_sizes = [5, 10, 100, 200];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("trie-nivc");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);

    let state = State::init_lurk_state().rccell();
    let mut lang = Lang::new();
    install(&state, &mut lang);
    let lang = Arc::new(lang);

    let store = Store::<Fr>::default();
    let expr = store.read(state, CODE).unwrap();

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);
    let frames = evaluate(
        Some((&lurk_step, &cprocs, &lang)),
        expr,
        &store,
        1_000_000,
        &dummy_terminal(),
    )
    .unwrap();

    assert_eq!(frames.last().unwrap().output[0], store.num_u64(12688603180));

    for size in batch_sizes {
        prove("rc", size, &lang, &store, &frames, &mut group);
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
            trie_nivc,
        }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
            trie_nivc,
        }
    }
}

criterion_main!(benches);
