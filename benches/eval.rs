use blstrs::Scalar as Fr;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lurk::{
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
        Evaluator,
    },
    field::LurkField,
    ptr::Ptr,
    store::Store,
};

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

fn criterion_benchmark(c: &mut Criterion) {
    let limit = 1_000_000_000;

    let lang_bls = Lang::<Fr, Coproc<Fr>>::new();
    let lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();

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

    // I'm not sure sure these make sense, since `vesta` isn't one of the base curves
    // we use in groth16/nova, so this store/curve variant will never be instantiated
    c.bench_function("eval_go_base_10_16_pasta_vesta", |b| {
        let mut store = Store::default();
        let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            let result =
                Evaluator::new(ptr, empty_sym_env(&store), &mut store, limit, &lang_vesta).eval();
            black_box(result)
        })
    });

    c.bench_function("eval_go_base_10_160_pasta_vesta", |b| {
        let mut store = Store::default();
        let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(160));

        b.iter(|| {
            let result =
                Evaluator::new(ptr, empty_sym_env(&store), &mut store, limit, &lang_vesta).eval();
            black_box(result)
        })
    });
}

criterion_group!{
    name = eval;
    config = Criterion::default();
    targets = criterion_benchmark
}
criterion_main!(eval);
