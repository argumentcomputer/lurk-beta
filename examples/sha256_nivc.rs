use pasta_curves::pallas::Scalar as Fr;
use std::{sync::Arc, time::Instant};
use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

use lurk::{
    coprocessor::sha256::{Sha256Coproc, Sha256Coprocessor},
    eval::lang::Lang,
    field::LurkField,
    lem::{
        eval::{evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig},
        multiframe::MultiFrame,
        pointers::Ptr,
        store::Store,
    },
    proof::{supernova::SuperNovaProver, Prover, RecursiveSNARKTrait},
    public_parameters::{
        instance::{Instance, Kind},
        supernova_public_params,
    },
    state::user_sym,
};

const REDUCTION_COUNT: usize = 10;

fn sha256_nivc<F: LurkField>(store: &Store<F>, n: usize, input: &[usize]) -> Ptr {
    assert_eq!(n, input.len());
    let input = input
        .iter()
        .map(|i| i.to_string())
        .collect::<Vec<String>>()
        .join(" ");
    let input = format!("({})", input);
    let program = format!(
        r#"
(letrec ((encode-1 (lambda (term) 
            (let ((type (car term))
                  (value (cdr term)))
                (if (eq 'sha256 type)
                    (eval (cons 'sha256_nivc_{n} value))
                    (if (eq 'lurk type)
                        (commit value)
                        (if (eq 'id type)
                            value))))))
      (encode (lambda (input)
                (if input
                    (cons 
                        (encode-1 (car input))
                        (encode (cdr input)))))))
  (encode '((sha256 . {input}))))
"#
    );

    store.read_with_default_state(&program).unwrap()
}

/// Run the example in this file with
/// `cargo run --release --example sha256_nivc <n>`
/// where `n` is the needed arity (default is 1)
fn main() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new());
    tracing::subscriber::set_global_default(subscriber).unwrap();

    let args = std::env::args().collect::<Vec<_>>();
    let n = args.get(1).unwrap_or(&"1".into()).parse().unwrap();

    let store = &Store::<Fr>::default();
    let cproc_sym = user_sym(&format!("sha256_nivc_{n}"));

    let call = sha256_nivc(store, n, &(0..n).collect::<Vec<_>>());

    let mut lang = Lang::<Fr, Sha256Coproc<Fr>>::new();
    lang.add_coprocessor(cproc_sym, Sha256Coprocessor::new(n));
    let lang_rc = Arc::new(lang.clone());

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);
    let frames = evaluate(Some((&lurk_step, &cprocs, &lang)), call, store, 1000).unwrap();

    let supernova_prover = SuperNovaProver::<Fr, Sha256Coproc<Fr>, MultiFrame<'_, _, _>>::new(
        REDUCTION_COUNT,
        lang_rc.clone(),
    );

    println!("Setting up running claim parameters (rc = {REDUCTION_COUNT})...");
    let pp_start = Instant::now();

    let instance_primary = Instance::new(REDUCTION_COUNT, lang_rc, true, Kind::SuperNovaAuxParams);
    let pp = supernova_public_params::<_, _, MultiFrame<'_, _, _>>(&instance_primary).unwrap();

    let pp_end = pp_start.elapsed();
    println!("Running claim parameters took {:?}", pp_end);

    println!("Beginning proof step...");
    let proof_start = Instant::now();
    let (proof, z0, zi, _num_steps) = tracing_texray::examine(tracing::info_span!("bang!"))
        .in_scope(|| supernova_prover.prove(&pp, &frames, store).unwrap());
    let proof_end = proof_start.elapsed();

    println!("Proofs took {:?}", proof_end);

    println!("Verifying proof...");

    let verify_start = Instant::now();
    assert!(proof.verify(&pp, &z0, &zi).unwrap());
    let verify_end = verify_start.elapsed();

    println!("Verify took {:?}", verify_end);

    println!("Compressing proof..");
    let compress_start = Instant::now();
    let compressed_proof = proof.compress(&pp).unwrap();
    let compress_end = compress_start.elapsed();

    println!("Compression took {:?}", compress_end);

    let buf = bincode::serialize(&compressed_proof).unwrap();
    println!("proof size : {:}B", buf.len());

    let compressed_verify_start = Instant::now();
    let res = compressed_proof.verify(&pp, &z0, &zi).unwrap();
    let compressed_verify_end = compressed_verify_start.elapsed();

    println!("Final verification took {:?}", compressed_verify_end);

    if res {
        println!(
            "Congratulations! You proved, verified, compressed, and verified (again!) an NIVC SHA256 hash calculation in {:?} time!",
            verify_end + proof_end + verify_end + compress_end
        );
    }
}
