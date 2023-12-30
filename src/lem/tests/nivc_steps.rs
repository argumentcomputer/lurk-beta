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
    tag::{ContTag, ExprTag},
};

#[test]
fn test_nivc_steps() {
    let mut lang = Lang::<Fr, DumbCoprocessor<Fr>>::new();
    let dumb = DumbCoprocessor::new();
    let name = user_sym("cproc-dumb");

    let store = Store::<Fr>::default();
    lang.add_coprocessor(name, dumb);

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);

    // this `Lang` only has one coprocessor, so we should get one `Func`
    assert_eq!(cprocs.len(), 1);
    let cproc = &cprocs[0];

    // 9^2 + 8 = 89
    let expr = store.read_with_default_state("(cproc-dumb 9 8)").unwrap();

    let frames = evaluate(Some((&lurk_step, &lang)), expr, &store, 10).unwrap();

    // Iteration 1: evaluate first argument
    // Iteration 2: evaluate second argument
    // Iteration 3: the list of arguments is empty, so set up coprocessor call
    // Iteration 4: reduce with coprocessor
    // Iteration 5: outermost -> terminal
    assert_eq!(frames.len(), 5);

    // this computation terminates
    assert!(matches!(
        frames[4].output[2].tag(),
        Tag::Cont(ContTag::Terminal)
    ));

    // `cproc` can't reduce the first input, which is meant for `lurk_step`
    let first_input = &frames[0].input;
    assert!(cproc.call_simple(first_input, &store, &lang, 0).is_err());

    // the fourth frame is the one reduced by the coprocessor
    let cproc_frame = &frames[3];
    assert_eq!(cproc_frame.pc, 1);
    let mut cproc_input = cproc_frame.input.clone();
    assert!(matches!(cproc_input[0].tag(), Tag::Expr(ExprTag::Cproc)));

    // `lurk_step` stutters on the cproc input
    let output = &lurk_step
        .call_simple(&cproc_input, &store, &lang, 0)
        .unwrap()
        .output;
    assert_eq!(&cproc_input, output);

    // `cproc` *can* reduce the cproc input
    let output = &cproc
        .call_simple(&cproc_input, &store, &lang, 1)
        .unwrap()
        .output;
    assert_ne!(&cproc_input, output);
    assert_eq!(output, &cproc_frame.output);

    // now, we set up a coprocessor call just like the previous one, except that
    // the coprocessor name is wrong
    let cont = cproc_input.pop().unwrap();
    let env = cproc_input.pop().unwrap();
    let expr = cproc_input.pop().unwrap();

    let idx = expr.get_index2().unwrap();
    let [_, args] = store.expect_2_ptrs(idx);
    let new_name = user_sym("cproc-dumb-not");
    let new_expr = store.intern_2_ptrs(
        Tag::Expr(ExprTag::Cproc),
        store.intern_symbol(&new_name),
        args,
    );

    // `cproc` can't reduce the altered cproc input (with the wrong name)
    let cproc_input = vec![new_expr, env, cont];
    assert!(cproc.call_simple(&cproc_input, &store, &lang, 0).is_err());
}
