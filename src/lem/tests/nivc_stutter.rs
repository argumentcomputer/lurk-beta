use pasta_curves::pallas::Scalar as Fr;

use crate::{
    coprocessor::test::DumbCoprocessor,
    eval::lang::Lang,
    lem::{
        eval::{evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig},
        store::Store,
        Tag,
    },
    state::user_sym,
    tag::ExprTag,
};

#[test]
fn test_nivc_stutter() {
    let mut lang = Lang::<Fr, DumbCoprocessor<Fr>>::new();
    let dumb = DumbCoprocessor::new();
    let name = user_sym("cproc-dumb");

    let store = Store::<Fr>::default();
    lang.add_coprocessor(name, dumb);

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);

    assert_eq!(cprocs.len(), 1);
    let cproc = &cprocs[0];

    // 9^2 + 8 = 89
    let expr = "(cproc-dumb 9 8)";
    let expr = store.read_with_default_state(expr).unwrap();

    let (frames, _) = evaluate(Some((&lurk_step, &lang)), expr, &store, 10).unwrap();

    assert_eq!(frames.len(), 5);

    // `cproc` can't reduce the first input
    let first_input = &frames[0].input;
    let output = &cproc
        .call_simple(first_input, &store, &lang, 0)
        .unwrap()
        .output;
    assert_eq!(first_input, output);

    // `lurk_step` can't reduce the cproc input
    let mut cproc_input = frames[3].input.clone();
    assert!(matches!(cproc_input[0].tag(), Tag::Expr(ExprTag::Cproc)));
    let output = &lurk_step
        .call_simple(&cproc_input, &store, &lang, 0)
        .unwrap()
        .output;
    assert_eq!(&cproc_input, output);

    // `cproc` can reduce the cproc input
    let output = &cproc
        .call_simple(&cproc_input, &store, &lang, 0)
        .unwrap()
        .output;
    assert_ne!(&cproc_input, output);

    // swapping the cproc name
    let cont = cproc_input.pop().unwrap();
    let env = cproc_input.pop().unwrap();
    let expr = cproc_input.pop().unwrap();

    let idx = expr.get_index2().unwrap();
    let (_, args) = store.expect_2_ptrs(idx);
    let new_name = user_sym("cproc-dumb-not");
    let expr = store.intern_2_ptrs(
        Tag::Expr(ExprTag::Cproc),
        store.intern_symbol(&new_name),
        *args,
    );

    // `cproc` can't reduce the altered cproc input (with the wrong name)
    let cproc_input = vec![expr, env, cont];
    let output = &cproc
        .call_simple(&cproc_input, &store, &lang, 0)
        .unwrap()
        .output;
    assert_eq!(&cproc_input, output);
}
