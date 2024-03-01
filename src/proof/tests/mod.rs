mod nova_tests;
mod supernova_tests;

use bellpepper::util_cs::{metric_cs::MetricCS, witness_cs::WitnessCS, Comparable};
use bellpepper_core::{test_cs::TestConstraintSystem, Circuit, ConstraintSystem, Delta};
use expect_test::Expect;
use std::sync::Arc;

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    lem::{eval::EvalConfig, pointers::Ptr, store::Store},
    proof::{
        nova::{public_params, CurveCycleEquipped, NovaProver, C1LEM},
        supernova::FoldingConfig,
        CEKState, EvaluationStore, FrameLike, Provable, Prover, RecursiveSNARKTrait,
    },
};

const DEFAULT_REDUCTION_COUNT: usize = 5;
const REDUCTION_COUNTS_TO_TEST: [usize; 3] = [1, 2, 5];

// Returns index of first mismatch, along with the mismatched elements if they exist.
fn mismatch<T: PartialEq + Copy>(a: &[T], b: &[T]) -> Option<(usize, (Option<T>, Option<T>))> {
    let min_len = a.len().min(b.len());
    for i in 0..min_len {
        if a[i] != b[i] {
            return Some((i, (Some(a[i]), Some(b[i]))));
        }
    }
    match (a.get(min_len), b.get(min_len)) {
        (Some(&a_elem), None) => Some((min_len, (Some(a_elem), None))),
        (None, Some(&b_elem)) => Some((min_len, (None, Some(b_elem)))),
        _ => None,
    }
}

fn test_aux<F: CurveCycleEquipped, C: Coprocessor<F>>(
    s: &Store<F>,
    expr: &str,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<&[Ptr]>,
    expected_iterations: &Expect,
    lang: &Option<Arc<Lang<F, C>>>,
) {
    for chunk_size in REDUCTION_COUNTS_TO_TEST {
        nova_test_full_aux::<F, C>(
            s,
            expr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            chunk_size,
            false,
            None,
            lang,
        )
    }
}

fn test_aux_ptr<F: CurveCycleEquipped, C: Coprocessor<F>>(
    s: &Store<F>,
    expr: Ptr,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<&[Ptr]>,
    expected_iterations: &Expect,
    lang: &Option<Arc<Lang<F, C>>>,
) {
    for chunk_size in REDUCTION_COUNTS_TO_TEST {
        nova_test_full_aux_ptr::<F, C>(
            s,
            expr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            chunk_size,
            false,
            None,
            lang,
        )
    }
}

fn nova_test_full_aux<F: CurveCycleEquipped, C: Coprocessor<F>>(
    s: &Store<F>,
    expr: &str,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<&[Ptr]>,
    expected_iterations: &Expect,
    reduction_count: usize,
    check_nova: bool,
    limit: Option<usize>,
    lang: &Option<Arc<Lang<F, C>>>,
) {
    let expr = EvaluationStore::read(s, expr).unwrap();

    nova_test_full_aux_ptr(
        s,
        expr,
        expected_result,
        expected_env,
        expected_cont,
        expected_emitted,
        expected_iterations,
        reduction_count,
        check_nova,
        limit,
        lang,
    );
}

fn nova_test_full_aux_ptr<F: CurveCycleEquipped, C: Coprocessor<F>>(
    s: &Store<F>,
    expr: Ptr,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<&[Ptr]>,
    expected_iterations: &Expect,
    reduction_count: usize,
    check_nova: bool,
    limit: Option<usize>,
    lang: &Option<Arc<Lang<F, C>>>,
) {
    let f = |l| {
        nova_test_full_aux2::<F, C>(
            s,
            expr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            reduction_count,
            check_nova,
            limit,
            l,
        )
    };

    if let Some(l) = lang {
        f(l.clone())
    } else {
        let lang = Lang::new();
        f(Arc::new(lang))
    };
}

fn nova_test_full_aux2<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    s: &'a Store<F>,
    expr: Ptr,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<&[Ptr]>,
    expected_iterations: &Expect,
    reduction_count: usize,
    check_nova: bool,
    limit: Option<usize>,
    lang: Arc<Lang<F, C>>,
) {
    let limit = limit.unwrap_or(10000);

    let e = s.initial_empty_env();

    let frames =
        C1LEM::<'a, F, C>::build_frames(expr, e, s, limit, &EvalConfig::new_ivc(&lang)).unwrap();
    let nova_prover = NovaProver::<'a, F, C>::new(reduction_count, lang.clone());

    if check_nova {
        let pp = public_params(reduction_count, lang.clone());
        let (proof, z0, zi, _num_steps) = nova_prover.prove_from_frames(&pp, &frames, s).unwrap();

        let res = proof.verify(&pp, &z0, &zi);
        if res.is_err() {
            tracing::debug!("{:?}", &res);
        }
        assert!(res.unwrap());

        let compressed: crate::proof::nova::Proof<F, C1LEM<'a, F, C>> =
            proof.compress(&pp).unwrap();
        let res2 = compressed.verify(&pp, &z0, &zi);

        assert!(res2.unwrap());
    }

    let folding_config = Arc::new(FoldingConfig::new_ivc(lang, nova_prover.reduction_count()));

    let multiframes = C1LEM::<'a, F, C>::from_frames(&frames, s, &folding_config);
    let len = multiframes.len();

    let expected_iterations_data = expected_iterations.data().parse::<usize>().unwrap();
    let adjusted_iterations = nova_prover.expected_num_steps(expected_iterations_data);
    let mut previous_frame: Option<&C1LEM<'a, F, C>> = None;

    let mut cs_blank = MetricCS::<F>::new();

    let blank = C1LEM::<'a, F, C>::blank(folding_config, 0);
    blank
        .synthesize(&mut cs_blank)
        .expect("failed to synthesize blank");

    for multiframe in multiframes.iter() {
        let mut cs = TestConstraintSystem::new();
        let mut wcs = WitnessCS::new();

        tracing::debug!("synthesizing test cs");
        multiframe.clone().synthesize(&mut cs).unwrap();
        tracing::debug!("synthesizing witness cs");
        multiframe.clone().synthesize(&mut wcs).unwrap();

        if let Some(prev) = previous_frame {
            assert!(prev.precedes(multiframe));
        };
        // tracing::debug!("frame {}" i);
        let unsat = cs.which_is_unsatisfied();
        if unsat.is_some() {
            // For some reason, this isn't getting printed from within the implementation as expected.
            // Since we always want to know this information, if the condition occurs, just print it here.
            tracing::debug!("{:?}", unsat);
        }
        assert!(cs.is_satisfied());
        assert!(cs.verify(&multiframe.public_inputs()));
        tracing::debug!("cs is satisfied!");
        let cs_inputs = cs.scalar_inputs();
        let cs_aux = cs.scalar_aux();

        let wcs_inputs = wcs.input_assignment();
        let wcs_aux = wcs.aux_assignment();

        assert_eq!(None, mismatch(&cs_inputs, wcs_inputs));
        assert_eq!(None, mismatch(&cs_aux, wcs_aux));

        previous_frame = Some(multiframe);

        let delta = cs.delta(&cs_blank, true);

        assert!(delta == Delta::Equal);
    }
    let output = previous_frame.unwrap().output();

    if let Some(expected_emitted) = expected_emitted {
        let mut emitted_vec = Vec::default();
        for frame in frames.iter() {
            emitted_vec.extend(C1LEM::<'a, F, C>::emitted(s, frame));
        }
        assert_eq!(expected_emitted, &emitted_vec);
    }

    if let Some(expected_result) = expected_result {
        assert!(s.ptr_eq(&expected_result, output.expr()));
    }
    if let Some(expected_env) = expected_env {
        assert!(s.ptr_eq(&expected_env, output.env()));
    }
    if let Some(expected_cont) = expected_cont {
        assert_eq!(&expected_cont, output.cont());
    } else {
        assert_eq!(&s.get_cont_terminal(), output.cont());
    }

    let iterations = C1LEM::<'a, F, C>::significant_frame_count(&frames);
    assert!(iterations <= expected_iterations_data);
    expected_iterations.assert_eq(&iterations.to_string());
    assert_eq!(adjusted_iterations, len);
}
