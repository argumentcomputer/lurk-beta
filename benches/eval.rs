use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lurk::{
    eval::{empty_sym_env, Evaluator},
    pool::{Pool, Ptr},
};

fn go_base(pool: &mut Pool, a: u64, b: u64) -> Ptr {
    let limit = 1000000;
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

    let ptr = pool.read(&program).unwrap();
    let (result, _new_env, _iterations, _continuation) =
        Evaluator::new(ptr, empty_sym_env(&*pool), pool, limit).eval();

    result
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("go_base_10_16", |b| {
        let mut pool = Pool::default();
        b.iter(|| go_base(&mut pool, black_box(10), black_box(16)))
    });

    c.bench_function("go_base_10_160", |b| {
        let mut pool = Pool::default();
        b.iter(|| go_base(&mut pool, black_box(10), black_box(160)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
