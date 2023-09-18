//! This benchmark measures the IVC performance of coprocessors, by adding a `sha256`
//! circuit alongside the lurk primary circuit. When supernova is integrated as a backend,
//! then NIVC performance can also be tested. This benchmark serves as a baseline for that
//! performance.
//!
//! Note: The example [example/sha256_ivc.rs] is this same benchmark but as an example
//! that's easier to play with and run.

use lurk::circuit::gadgets::data::GlobalAllocations;
use lurk::state::user_sym;
use lurk::{circuit::gadgets::pointer::AllocatedContPtr, tag::Tag};
use std::{cell::RefCell, marker::PhantomData, rc::Rc, sync::Arc, time::Duration};

use bellpepper::gadgets::{multipack::pack_bits, sha256::sha256};
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use camino::Utf8Path;
use criterion::{
    black_box, criterion_group, criterion_main, measurement, BatchSize, BenchmarkGroup,
    BenchmarkId, Criterion, SamplingMode,
};

use lurk_macros::Coproc;
use pasta_curves::pallas::Scalar as Fr;

use lurk::{
    circuit::gadgets::pointer::AllocatedPtr,
    coprocessor::{CoCircuit, Coprocessor},
    eval::{empty_sym_env, lang::Lang},
    field::LurkField,
    proof::nova::NovaProver,
    proof::Prover,
    ptr::Ptr,
    public_parameters::public_params,
    state::State,
    store::Store,
    tag::ExprTag,
    Num,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const PUBLIC_PARAMS_PATH: &str = "/var/tmp/lurk_benches/public_params";

fn sha256_ivc<F: LurkField>(
    store: &mut Store<F>,
    state: Rc<RefCell<State>>,
    arity: usize,
    n: usize,
    input: Vec<usize>,
) -> Ptr<F> {
    assert_eq!(n, input.len());
    let input = input
        .iter()
        .map(|i| format!("(sha256 . {i})"))
        .collect::<Vec<String>>()
        .join(" ");
    let input = format!("'({})", input);
    let program = format!(
        r#"
(letrec ((encode-1 (lambda (term) 
            (let ((type (car term))
                  (value (cdr term)))
                (if (eq 'sha256 type)
                    (eval (cons 'sha256_ivc_{arity} value))
                    (if (eq 'lurk type)
                        (commit value)
                        (if (eq 'id type)
                            value))))))
        (encode (lambda (input)
                (if input
                    (cons 
                        (encode-1 (car input))
                        (encode (cdr input)))))))
  (encode '((lurk . 5) (id . 15) {input})))
"#
    );

    store.read_with_state(state, &program).unwrap()
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct Sha256Coprocessor<F: LurkField> {
    arity: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {
    fn arity(&self) -> usize {
        self.arity
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        _store: &Store<F>,
        input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let zero = Boolean::constant(false);

        let mut bits = vec![];

        // println!("{:?}", input_exprs);

        for input_ptr in input_exprs {
            let tag_bits = input_ptr
                .tag()
                .to_bits_le_strict(&mut cs.namespace(|| "preimage_tag_bits"))?;
            let hash_bits = input_ptr
                .hash()
                .to_bits_le_strict(&mut cs.namespace(|| "preimage_hash_bits"))?;

            bits.extend(tag_bits);
            bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
            bits.extend(hash_bits);
            bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
        }

        bits.reverse();

        let mut digest_bits = sha256(cs.namespace(|| "digest_bits"), &bits)?;

        digest_bits.reverse();

        // Fine to lose the last <1 bit of precision.
        let digest_scalar = pack_bits(cs.namespace(|| "digest_scalar"), &digest_bits)?;
        let output_expr = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "output_expr"),
            ExprTag::Num.to_field(),
            digest_scalar,
        )?;
        Ok((output_expr, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        self.arity
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let mut hasher = <Sha256 as sha2::Digest>::new();

        let mut input = vec![0u8; 64 * self.arity];

        for (i, input_ptr) in args.iter().enumerate() {
            let input_zptr = s.hash_expr(input_ptr).unwrap();
            let tag_zptr: F = input_zptr.tag().to_field();
            let hash_zptr = input_zptr.value();
            input[(64 * i)..(64 * i + 32)].copy_from_slice(&tag_zptr.to_bytes());
            input[(64 * i + 32)..(64 * (i + 1))].copy_from_slice(&hash_zptr.to_bytes());
        }

        input.reverse();

        hasher.update(input);
        let mut bytes = hasher.finalize();
        bytes.reverse();
        let l = bytes.len();
        // Discard the two most significant bits.
        bytes[l - 1] &= 0b00111111;

        let scalar = F::from_bytes(&bytes).unwrap();
        let result = Num::from_scalar(scalar);

        s.intern_num(result)
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

impl<F: LurkField> Sha256Coprocessor<F> {
    pub(crate) fn new(arity: usize) -> Self {
        Self {
            arity,
            _p: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
enum Sha256Coproc<F: LurkField> {
    SC(Sha256Coprocessor<F>),
}

struct ProveParams {
    arity: usize,
    n: usize,
    reduction_count: usize,
}

impl ProveParams {
    fn name(&self) -> String {
        let date = env!("VERGEN_GIT_COMMIT_DATE");
        let sha = env!("VERGEN_GIT_SHA");
        format!(
            "{date}:{sha}:rc={}:sha256_ivc_{}",
            self.reduction_count, self.arity
        )
    }
}

fn sha256_ivc_prove<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
    state: Rc<RefCell<State>>,
) {
    let ProveParams {
        arity,
        n: _,
        reduction_count,
    } = prove_params;

    let limit = 10000;

    let store = &mut Store::<Fr>::new();
    let cproc_sym = user_sym(&format!("sha256_ivc_{arity}"));

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(cproc_sym, Sha256Coprocessor::new(arity).into())],
    );
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let pp = public_params(
        reduction_count,
        true,
        lang_rc.clone(),
        Utf8Path::new(PUBLIC_PARAMS_PATH),
    )
    .unwrap();

    c.bench_with_input(
        BenchmarkId::new(prove_params.name(), arity),
        &prove_params,
        |b, prove_params| {
            let env = empty_sym_env(store);
            let ptr = sha256_ivc(
                store,
                state.clone(),
                black_box(prove_params.arity),
                black_box(prove_params.n),
                (0..prove_params.n).collect(),
            );

            let prover = NovaProver::new(prove_params.reduction_count, lang.clone());

            let frames = &prover
                .get_evaluation_frames(ptr, env, store, limit, lang_rc.clone())
                .unwrap();

            b.iter_batched(
                || (frames, lang_rc.clone()),
                |(frames, lang_rc)| {
                    let result = prover.prove(&pp, frames, store, lang_rc);
                    let _ = black_box(result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn prove_benchmarks(c: &mut Criterion) {
    tracing::debug!("{:?}", &*lurk::config::CONFIG);
    let reduction_counts = vec![10, 100];
    let batch_sizes = vec![1, 2, 5, 10, 20];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("prove");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    let state = State::init_lurk_state().rccell();

    for &n in batch_sizes.iter() {
        for &reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                arity: 1,
                n,
                reduction_count,
            };
            sha256_ivc_prove(prove_params, &mut group, state.clone());
        }
    }
}

fn sha256_ivc_prove_compressed<M: measurement::Measurement>(
    prove_params: ProveParams,
    c: &mut BenchmarkGroup<'_, M>,
    state: Rc<RefCell<State>>,
) {
    let ProveParams {
        arity,
        n: _,
        reduction_count,
    } = prove_params;

    let limit = 10000;

    let store = &mut Store::<Fr>::new();
    let cproc_sym = user_sym(&format!("sha256_ivc_{arity}"));

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(cproc_sym, Sha256Coprocessor::new(arity).into())],
    );
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let pp = public_params(
        reduction_count,
        true,
        lang_rc.clone(),
        Utf8Path::new(PUBLIC_PARAMS_PATH),
    )
    .unwrap();

    c.bench_with_input(
        BenchmarkId::new(prove_params.name(), arity),
        &prove_params,
        |b, prove_params| {
            let env = empty_sym_env(store);
            let ptr = sha256_ivc(
                store,
                state.clone(),
                black_box(prove_params.arity),
                black_box(prove_params.n),
                (0..prove_params.n).collect(),
            );

            let prover = NovaProver::new(prove_params.reduction_count, lang.clone());

            let frames = &prover
                .get_evaluation_frames(ptr, env, store, limit, lang_rc.clone())
                .unwrap();

            b.iter_batched(
                || (frames, lang_rc.clone()),
                |(frames, lang_rc)| {
                    let (proof, _, _, _) = prover.prove(&pp, frames, store, lang_rc).unwrap();
                    let compressed_result = proof.compress(&pp).unwrap();

                    let _ = black_box(compressed_result);
                },
                BatchSize::LargeInput,
            )
        },
    );
}

fn prove_compressed_benchmarks(c: &mut Criterion) {
    tracing::debug!("{:?}", &*lurk::config::CONFIG);
    let reduction_counts = vec![10, 100];
    let batch_sizes = vec![1, 2, 5, 10, 20];
    let mut group: BenchmarkGroup<'_, _> = c.benchmark_group("prove_compressed");
    group.sampling_mode(SamplingMode::Flat); // This can take a *while*
    group.sample_size(10);
    let state = State::init_lurk_state().rccell();

    for &n in batch_sizes.iter() {
        for &reduction_count in reduction_counts.iter() {
            let prove_params = ProveParams {
                arity: 1,
                n,
                reduction_count,
            };
            sha256_ivc_prove_compressed(prove_params, &mut group, state.clone());
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
                prove_benchmarks,
                prove_compressed_benchmarks
         }
    } else {
        criterion_group! {
            name = benches;
            config = Criterion::default()
            .measurement_time(Duration::from_secs(120))
            .sample_size(10);
            targets =
                prove_benchmarks,
                prove_compressed_benchmarks
         }
    }
}

criterion_main!(benches);
