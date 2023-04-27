use blstrs::Scalar as Fr;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lurk::{
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
    },
    field::LurkField,
    ptr::Ptr,
    store::Store,
    proof::{nova::{NovaProver, public_params}, groth16::Groth16Prover},
    proof::Prover,
};

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

fn criterion_benchmark(c: &mut Criterion) {
    let limit = 1_000_000_000;

    let lang_bls = Lang::<Fr, Coproc<Fr>>::new();
    let lang_pallas = Lang::<pasta_curves::Fp, Coproc<pasta_curves::Fp>>::new();
    let lang_vesta = Lang::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>::new();

    let reduction_count = DEFAULT_REDUCTION_COUNT;
    
    c.bench_function("prove_go_base_10_16_nova", |b| {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let ptr = go_base::<pasta_curves::Fq>(&mut store, black_box(10), black_box(16));
        let prover = NovaProver::new(reduction_count, lang_vesta.clone());
        
        let pp = public_params(reduction_count, &lang_vesta);
        let frames = prover
            .get_evaluation_frames(ptr, env, &mut store, limit, &lang_vesta)
            .unwrap();

        b.iter(|| {
            black_box(prover.prove(&pp, frames.clone(), &mut store, &lang_vesta).unwrap());
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
