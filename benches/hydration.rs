use blstrs::Scalar as Fr;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lurk::{
    field::LurkField,
    ptr::Ptr,
    store::Store,
};

// NOTE: update this after store PR is merged, since "hydration" will be merged
// with just interning into `ZStore`

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

    c.bench_function("hydration_go_base_10_16_bls12", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            black_box(store.hydrate_scalar_cache())
        })
    });

    c.bench_function("hydration_go_base_10_160_bls12", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<Fr>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            black_box(store.hydrate_scalar_cache())
        })
    });

    c.bench_function("hydration_go_base_10_16_pasta_pallas", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(16));

        b.iter(|| {
            black_box(store.hydrate_scalar_cache())
        })
    });

    c.bench_function("hydration_go_base_10_160_pasta_pallas", |b| {
        let mut store = Store::default();
        let _ptr = go_base::<pasta_curves::Fp>(&mut store, black_box(10), black_box(160));

        b.iter(|| {
            black_box(store.hydrate_scalar_cache())
        })
    });
}

criterion_group!{
    name = hydration;
    config = Criterion::default().sample_size(60);
    targets = criterion_benchmark
}
criterion_main!(hydration);
