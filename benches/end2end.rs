use blstrs::Scalar as Fr;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

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
    store::Store,
};
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
    let limit = 1_000_000_000;
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    c.bench_function("end2end_go_base_10_16_nova", |b| {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(0));
        let prover = NovaProver::new(reduction_count, lang_vesta.clone());

        // use cached public params
        let pp = fcomm::public_params(reduction_count).unwrap();

        b.iter(|| {
            let result = prover
                .evaluate_and_prove(&pp, ptr, env, &mut store, limit, &lang_vesta)
                .unwrap();
            black_box(result);
        })
    });
}

fn store_benchmark(c: &mut Criterion) {
    c.bench_function("store_go_base_10_16_bls12", |b| {
        let mut store = Store::default();

        b.iter(|| {
            let ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));
            black_box(ptr)
        })
    });

    c.bench_function("store_go_base_10_160_bls12", |b| {
        let mut store = Store::default();

        b.iter(|| {
            let ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));
            black_box(ptr)
        })
    });

    c.bench_function("store_go_base_10_16_pasta_pallas", |b| {
        let mut store = Store::default();

        b.iter(|| {
            let ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(16));
            black_box(ptr)
        })
    });

    c.bench_function("store_go_base_10_160_pasta_pallas", |b| {
        let mut store = Store::default();

        b.iter(|| {
            let ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(160));
            black_box(ptr)
        })
    });
}

fn hydration_benchmark(c: &mut Criterion) {
    c.bench_function("hydration_go_base_10_16_bls12", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            store.hydrate_scalar_cache();
            black_box(())
        })
    });

    c.bench_function("hydration_go_base_10_160_bls12", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            store.hydrate_scalar_cache();
            black_box(())
        })
    });

    c.bench_function("hydration_go_base_10_16_pasta_pallas", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            store.hydrate_scalar_cache();
            black_box(())
        })
    });

    c.bench_function("hydration_go_base_10_160_pasta_pallas", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(160));

        b.iter(|| {
            store.hydrate_scalar_cache();
            black_box(())
        })
    });
}

fn eval_benchmark(c: &mut Criterion) {
    let limit = 1_000_000_000;

    let lang_bls = Lang::<Fr, Coproc<Fr>>::new();
    let lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();

    c.bench_function("eval_go_base_10_16_bls12", |b| {
        let mut store = Store::default();
        let ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            let result =
                Evaluator::new(ptr, empty_sym_env(&store), &mut store, limit, &lang_bls).eval();
            black_box(result)
        })
    });

    c.bench_function("eval_go_base_10_160_bls12", |b| {
        let mut store = Store::default();
        let ptr = go_base::<Fr>(&mut store, black_box(10), black_box(160));

        b.iter(|| {
            let result =
                Evaluator::new(ptr, empty_sym_env(&store), &mut store, limit, &lang_bls).eval();
            black_box(result)
        })
    });

    c.bench_function("eval_go_base_10_16_pasta_pallas", |b| {
        let mut store = Store::default();
        let ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            let result =
                Evaluator::new(ptr, empty_sym_env(&store), &mut store, limit, &lang_pallas).eval();
            black_box(result)
        })
    });

    c.bench_function("eval_go_base_10_160_pasta_pallas", |b| {
        let mut store = Store::default();
        let ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(160));

        b.iter(|| {
            let result =
                Evaluator::new(ptr, empty_sym_env(&store), &mut store, limit, &lang_pallas).eval();
            black_box(result)
        })
    });
}

fn circuit_generation_benchmark(c: &mut Criterion) {
    let limit = 1_000_000_000;

    let _lang_bls = Lang::<Fr, Coproc<Fr>>::new();
    let _lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();

    let reduction_count = DEFAULT_REDUCTION_COUNT;

    c.bench_function("prove_go_base_10_16_nova", |b| {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(16));
        let prover = NovaProver::new(reduction_count, lang_vesta.clone());

        let pp = fcomm::public_params(reduction_count).unwrap();
        let frames = prover
            .get_evaluation_frames(ptr, env, &mut store, limit, &lang_vesta)
            .unwrap();

        b.iter(|| {
            black_box(
                prover
                    .prove(&pp, frames.clone(), &mut store, &lang_vesta)
                    .unwrap(),
            );
        })
    });
}

fn prove_benchmark(c: &mut Criterion) {
    let limit = 1_000_000_000;
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();
    let reduction_count = DEFAULT_REDUCTION_COUNT;

    c.bench_function("prove_go_base_10_16_nova", |b| {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(0));
        let prover = NovaProver::new(reduction_count, lang_vesta.clone());

        let pp = fcomm::public_params(reduction_count).unwrap();
        let frames = prover
            .get_evaluation_frames(ptr, env, &mut store, limit, &lang_vesta)
            .unwrap();

        b.iter(|| {
            let result = prover
                .prove(&pp, frames.clone(), &mut store, &lang_vesta)
                .unwrap();
            black_box(result);
        })
    });
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
            end2end_benchmark,
            store_benchmark,
            hydration_benchmark,
            eval_benchmark,
            circuit_generation_benchmark,
            prove_benchmark
        }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
        targets =
            end2end_benchmark,
            store_benchmark,
            hydration_benchmark,
            eval_benchmark,
            circuit_generation_benchmark,
            prove_benchmark
        }
    }
}

criterion_main!(benches);
