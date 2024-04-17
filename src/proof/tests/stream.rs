use expect_test::{expect, Expect};
use halo2curves::bn256::Fr;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::sync::Arc;

use crate::{
    dual_channel::{dummy_terminal, pair_terminals},
    lang::{Coproc, Lang},
    lem::{
        eval::{evaluate_simple, resume_stream, start_stream},
        pointers::Ptr,
        store::Store,
    },
    proof::{supernova::SuperNovaProver, RecursiveSNARKTrait},
    public_parameters::{instance::Instance, supernova_public_params},
};

const LIMIT: usize = 200;

fn get_callable(callable_str: &str, store: &Store<Fr>) -> Ptr {
    let callable = store.read_with_default_state(callable_str).unwrap();
    let (io, _) =
        evaluate_simple::<Fr, Coproc<Fr>>(None, callable, store, LIMIT, &dummy_terminal()).unwrap();
    io[0]
}

#[inline]
fn expect_eq(computed: usize, expected: &Expect) {
    expected.assert_eq(&computed.to_string());
}

#[test]
fn test_continued_proof() {
    let callable_str = "(letrec ((add (lambda (counter x)
            (let ((counter (+ counter x)))
            (cons counter (add counter))))))
        (add 0))";
    let store = Arc::new(Store::<Fr>::default());
    let callable = get_callable(callable_str, &store);
    let expected_iterations = &expect!["14"];

    let lang = Arc::new(Lang::<Fr, Coproc<Fr>>::new());

    [1, 3, 5].into_par_iter().for_each(|rc| {
        let prover = SuperNovaProver::new(rc, lang.clone());
        let instance = Instance::new_supernova(&prover, true);
        let pp = supernova_public_params(&instance).unwrap();

        let (t1, t2) = pair_terminals();
        t2.send(store.num_u64(123)).unwrap();
        let frames = start_stream::<Fr, Coproc<Fr>>(None, callable, &store, LIMIT, &t1).unwrap();

        // this input will be used to construct the public input of every proof
        let z0 = store.to_scalar_vector(&frames.first().unwrap().input);

        expect_eq(frames.len(), expected_iterations);
        let output = &frames.last().unwrap().output;
        let (result, _) = store.fetch_cons(&output[0]).unwrap();
        assert_eq!(result, &store.num_u64(123));

        let (proof, ..) = prover
            .prove_from_frames(&pp, &frames, &store, None)
            .unwrap();

        proof
            .verify(&pp, &z0, &store.to_scalar_vector(output))
            .unwrap();

        let base_snark = proof.get_recursive();
        assert!(base_snark.is_some());

        // into the next stream cycle
        t2.send(store.intern_nil()).unwrap(); // send nil to skip stuttering
        t2.send(store.num_u64(321)).unwrap();
        let frames =
            resume_stream::<Fr, Coproc<Fr>>(None, output.clone(), &store, LIMIT, &t1).unwrap();

        expect_eq(frames.len(), expected_iterations);
        let output = &frames.last().unwrap().output;
        let (result, _) = store.fetch_cons(&output[0]).unwrap();
        assert_eq!(result, &store.num_u64(444));

        let (proof, ..) = prover
            .prove_from_frames(&pp, &frames, &store, base_snark)
            .unwrap();

        let zi = store.to_scalar_vector(output);
        proof.verify(&pp, &z0, &zi).unwrap();

        let proof = proof.compress(&pp).unwrap();
        proof.verify(&pp, &z0, &zi).unwrap();
    });
}
