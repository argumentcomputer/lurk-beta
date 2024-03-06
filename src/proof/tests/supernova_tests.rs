use halo2curves::bn256::Fr;
use std::sync::Arc;

use crate::{
    dual_channel::dummy_terminal,
    lang::Lang,
    lem::{
        eval::{evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig},
        store::Store,
    },
    proof::{supernova::SuperNovaProver, RecursiveSNARKTrait},
    public_parameters::{instance::Instance, supernova_public_params},
    state::user_sym,
};

#[test]
fn test_nil_nil_lang() {
    use crate::coprocessor::test::NilNil;
    let mut lang = Lang::<Fr, NilNil<Fr>>::new();
    lang.add_coprocessor(user_sym("nil-nil"), NilNil::new());

    let eval_config = EvalConfig::new_nivc(&lang);
    let lurk_step = make_eval_step_from_config(&eval_config);
    let cprocs = make_cprocs_funcs_from_lang(&lang);

    let store = Store::default();
    let expr = store.read_with_default_state("(nil-nil)").unwrap();
    let frames = evaluate(
        Some((&lurk_step, &cprocs, &lang)),
        expr,
        &store,
        50,
        &dummy_terminal(),
    )
    .unwrap();

    // iteration 1: main circuit sets up a call to the coprocessor
    // iteration 2: coprocessor does its job
    // iteration 3: main circuit sets termination to terminal
    assert_eq!(frames.len(), 3);

    let first_frame = frames.first().unwrap();
    let last_frame = frames.last().unwrap();
    let output = &last_frame.output;

    // the result is the (nil . nil) pair
    let nil = store.intern_nil();
    assert!(store.ptr_eq(&output[0], &store.cons(nil, nil)));

    // computation must end with the terminal continuation
    assert!(store.ptr_eq(&output[2], &store.cont_terminal()));

    let supernova_prover = SuperNovaProver::new(5, Arc::new(lang));
    let instance = Instance::new_supernova(&supernova_prover, true);
    let pp = supernova_public_params(&instance).unwrap();

    let (proof, ..) = supernova_prover
        .prove_from_frames(&pp, &frames, &store)
        .unwrap();

    let input_scalar = store.to_scalar_vector(&first_frame.input);
    let output_scalar = store.to_scalar_vector(output);

    // uncompressed proof verifies
    assert!(proof.verify(&pp, &input_scalar, &output_scalar).unwrap());

    // compressed proof verifies
    let proof = proof.compress(&pp).unwrap();
    assert!(proof.verify(&pp, &input_scalar, &output_scalar).unwrap());
}
