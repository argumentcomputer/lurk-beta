use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lurk::{
    eval::{empty_sym_env, Evaluator},
    pool::{Pool, Ptr},
};

fn go_base(pool: &mut Pool, a: u64, b: u64) -> Ptr {
    let program = format!(
        r#"
(let* ((foo (lambda (a b)
              (letrec* ((aux (lambda (i a x)
                               (if (= i b)
                                     x
                                     (let* ((x (+ x a))
                                            (a (+ a (* b 2))))
                                       (aux (+ i 1) a x))))))
                       (let* ((x (+ (* a b) 4)))
                         (aux 0 a x))))))
  (foo {} {}))
"#,
        a, b
    );

    pool.read(&program).unwrap()
}

fn criterion_benchmark(c: &mut Criterion) {
    let limit = 1_000_000_000;

    c.bench_function("go_base_10_16", |b| {
        let mut pool = Pool::default();
        let ptr = go_base(&mut pool, black_box(10), black_box(16));

        b.iter(|| {
            let result = Evaluator::new(ptr, empty_sym_env(&pool), &mut pool, limit).eval();
            black_box(result)
        })
    });

    c.bench_function("go_base_10_160", |b| {
        let mut pool = Pool::default();
        let ptr = go_base(&mut pool, black_box(10), black_box(160));

        b.iter(|| {
            let result = Evaluator::new(ptr, empty_sym_env(&pool), &mut pool, limit).eval();
            black_box(result)
        })
    });

    c.bench_function("go_base_10_320", |b| {
        let mut pool = Pool::default();
        let ptr = go_base(&mut pool, black_box(10), black_box(320));

        b.iter(|| {
            let result = Evaluator::new(ptr, empty_sym_env(&pool), &mut pool, limit).eval();
            black_box(result)
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
