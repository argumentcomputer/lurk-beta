use crate::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{eval::{compute_frame, eval_step, evaluate_simple}, pointers::Ptr, store::Store},
};

pub fn fib_expr<F: LurkField>(store: &Store<F>) -> Ptr {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
         (fib (next 0 1)))
  (fib))
"#;

    store.read_with_default_state(program).unwrap()
}

const LIN_COEF: usize = 11;
const ANG_COEF: usize = 10;

// The env output in the `fib_frame`th frame of the above, infinite Fibonacci computation contains a binding of the
// nth Fibonacci number to `a`.
pub fn fib_frame(n: usize) -> usize {
    LIN_COEF + ANG_COEF * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
pub fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}

pub fn compute_coeff<F: LurkField>(store: &Store<F>) -> (usize, usize) {
    let mut input = vec![fib_expr(store), store.intern_nil(), store.cont_outermost()];
    let lang: Lang<F, Coproc<F>> = Lang::new();
    loop {
        // TODO
        let (frame, _) =
            compute_frame(eval_step(), &[], &input, store, &lang, &mut vec![], 0).unwrap();

        input = frame.output.clone();
        let expr = frame.output[0];
        break;
    }
    (0, 0)
}

pub fn lurk_fib<F: LurkField>(store: &Store<F>, n: usize) -> Ptr {
    let frame_idx = fib_frame(n);
    let limit = frame_idx;
    let fib_expr = fib_expr(store);

    let (output, ..) = evaluate_simple::<F, Coproc<F>>(None, fib_expr, store, limit).unwrap();

    let target_env = &output[1];

    // The result is the value of the second binding (of `A`), in the target env.
    // See relevant excerpt of execution trace below:
    //
    // INFO  lurk::eval > Frame: 11
    // Expr: (NEXT B (+ A B))
    // Env: ((B . 1) (A . 0) ((NEXT . <FUNCTION (A) (LAMBDA (B) (NEXT B (+ A B)))>)))
    // Cont: Tail{ saved_env: (((NEXT . <FUNCTION (A) (LAMBDA (B) (NEXT B (+ A B)))>))), continuation: LetRec{var: FIB,
    //       saved_env: (((NEXT . <FUNCTION (A) (LAMBDA (B) (NEXT B (+ A B)))>))), body: (FIB), continuation: Tail{ saved_env:
    //       NIL, continuation: Outermost } } }

    let (_, rest_bindings) = store.car_cdr(target_env).unwrap();
    let (second_binding, _) = store.car_cdr(&rest_bindings).unwrap();
    store.car_cdr(&second_binding).unwrap().1
}

#[cfg(test)]
mod tests {
    use crate::{lem::store::Store, fib::lurk_fib};

    #[test]
    fn test_fib_io_matches() {
        let store = Store::<pasta_curves::Fq>::default();
        let fib_9 = store.num_u64(34);
        let fib_10 = store.num_u64(55);
        assert_eq!(fib_9, lurk_fib(&store, 9));
        assert_eq!(fib_10, lurk_fib(&store, 10));
    }
}
