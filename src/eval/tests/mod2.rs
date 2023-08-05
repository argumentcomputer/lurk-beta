use std::rc::Rc;

use crate::{
    coprocessor::Coprocessor,
    eval::{
        lang::{Coproc, Lang},
        Evaluator, IO,
    },
    field::LurkField,
    ptr::Ptr,
    state::State,
    store::Store,
    writer::Write,
};

#[inline]
fn print_to_string<F: LurkField>(ptr: Ptr<F>, store: &Store<F>, state: &State) -> String {
    // TODO
    ptr.fmt_to_string(store)
}

enum TestOutput {
    Error,
    Success {
        expr: Option<&'static str>,
        env: Option<&'static str>,
    },
}

struct TestInstance<F: LurkField, C: Coprocessor<F> + 'static> {
    input: &'static str,
    output: TestOutput,
    iterations: Option<usize>,
    emitted: Option<Vec<&'static str>>,
    lang: Rc<Lang<F, C>>,
}

const LIMIT: usize = 100000;

impl<F: LurkField, C: Coprocessor<F>> TestInstance<F, C> {
    fn assert_satisfied(&self, store: &mut Store<F>, state: &mut State) {
        let expr = store.read_with_state(state, self.input).unwrap();
        let (
            IO {
                expr: expr_ptr,
                env: env_ptr,
                cont: cont_ptr,
            },
            iterations,
            emitted,
        ) = Evaluator::new(expr, store.nil_ptr(), store, LIMIT, &self.lang)
            .eval()
            .unwrap();
        match self.output {
            TestOutput::Error => assert_eq!(store.get_cont_error(), cont_ptr),
            TestOutput::Success {
                expr: expr_expc,
                env: env_expc,
            } => {
                if let Some(expr_expc) = expr_expc {
                    assert_eq!(expr_expc, print_to_string(expr_ptr, store, state))
                }
                if let Some(env_expc) = env_expc {
                    assert_eq!(env_expc, print_to_string(env_ptr, store, state))
                }
            }
        }
        if let Some(iterations_expc) = self.iterations {
            assert_eq!(iterations_expc, iterations)
        }
        if let Some(emitted_expc) = &self.emitted {
            assert_eq!(emitted_expc.len(), emitted.len());
            for (emitted_expc, emitted) in emitted_expc.iter().zip(emitted) {
                assert_eq!(*emitted_expc, print_to_string(emitted, store, state));
            }
        }
    }
}

fn build_test_set<F: LurkField, C: Coprocessor<F>>() -> [TestInstance<F, Coproc<F>>; 3] {
    let default_lang = Rc::new(Lang::<F, Coproc<F>>::new());
    let simple = |source: &'static str, output: &'static str| TestInstance {
        input: source,
        output: TestOutput::Success {
            expr: Some(output),
            env: None,
        },
        iterations: None,
        emitted: None,
        lang: default_lang.clone(),
    };
    let error = |source: &'static str| TestInstance {
        input: source,
        output: TestOutput::Error,
        iterations: None,
        emitted: None,
        lang: default_lang.clone(),
    };
    [
        simple("nil", "nil"),
        simple(
            "(letrec ((exp (lambda (base exponent)
                            (if (= 0 exponent)
                                1
                                (* base (exp base (- exponent 1))))))
                    (exp2 (lambda (base exponent)
                            (if (= 0 exponent)
                                1
                                (* base (exp2 base (- exponent 1))))))
                    (exp3 (lambda (base exponent)
                            (if (= 0 exponent)
                                1
                                (* base (exp3 base (- exponent 1)))))))
                (+ (+ (exp 3 2) (exp2 2 3))
                (exp3 4 2)))",
            "33",
        ),
        error("(nil nil)"),
    ]
}

#[test]
fn assert_test_set() {
    use pasta_curves::pallas::Scalar;
    let test_set: [TestInstance<Scalar, Coproc<Scalar>>; 3] =
        build_test_set::<Scalar, Coproc<Scalar>>();
    let store = &mut Store::default();
    let state = &mut State::initial_lurk_state();
    test_set
        .iter()
        .for_each(|t| t.assert_satisfied(store, state));
}
