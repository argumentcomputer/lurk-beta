use lurk::{
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
};

pub(crate) fn fib_expr<F: LurkField>(store: &Store<F>) -> Ptr {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
         (fib (next 0 1)))
  (fib))
"#;

    store.read_with_default_state(program).unwrap()
}

const LIN_COEF: usize = 7;
const ANG_COEF: usize = 10;

// The env output in the `fib_frame`th frame of the above, infinite Fibonacci computation contains a binding of the
// nth Fibonacci number to `a`.
pub(crate) fn fib_frame(n: usize) -> usize {
    LIN_COEF + ANG_COEF * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
pub(crate) fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}

#[cfg(test)]
mod tests {
    use lurk::{
        eval::lang::{Coproc, Lang},
        lem::eval::{eval_step, evaluate_simple},
        state::user_sym,
    };

    use super::*;

    fn lurk_fib<F: LurkField>(store: &Store<F>, n: usize) -> Ptr {
        let frame_idx = fib_frame(n);
        let limit = frame_idx;
        let fib_expr = fib_expr(store);

        let (output, ..) = evaluate_simple::<F, Coproc<F>>(None, fib_expr, store, limit).unwrap();

        let target_env = &output[1];

        // The result is the value of the second binding (of `a`), in the target env.
        // See relevant excerpt of execution trace below:
        //
        // INFO lurk::lem::eval: Frame: 7
        // Expr: (.lurk.user.next .lurk.user.b (+ .lurk.user.a .lurk.user.b))
        // Env:  ((.lurk.user.b . 1) (.lurk.user.a . 0) ((.lurk.user.next . <FUNCTION (.lurk.user.a .lurk.user.b) (.lurk.user.next .lurk.user.b (+ .lurk.user.a .lurk.user.b))>)))
        // Cont: LetRec{ var: .lurk.user.fib,
        //               saved_env: (((.lurk.user.next . <FUNCTION (.lurk.user.a .lurk.user.b) (.lurk.user.next .lurk.user.b (+ .lurk.user.a .lurk.user.b))>))),
        //               body: (.lurk.user.fib), continuation: Outermost }

        let (_, rest_bindings) = store.car_cdr(target_env).unwrap();
        let (second_binding, _) = store.car_cdr(&rest_bindings).unwrap();
        store.car_cdr(&second_binding).unwrap().1
    }

    // Returns the linear and angular coefficients for the iteration count of fib
    fn compute_coeffs<F: LurkField>(store: &Store<F>) -> (usize, usize) {
        let mut input = vec![fib_expr(store), store.intern_nil(), store.cont_outermost()];
        let lang: Lang<F, Coproc<F>> = Lang::new();
        let mut coef_lin = 0;
        let coef_ang;
        let step_func = eval_step();
        let mut iteration = 0;
        loop {
            if let Some((elts, _)) = store.fetch_list(&input[0]) {
                if store.fetch_symbol(&elts[0]) == Some(user_sym("next"))
                    && store.fetch_symbol(&elts[1]) == Some(user_sym("b"))
                {
                    if coef_lin == 0 {
                        // first occurrence of `(next b ...)`
                        coef_lin = iteration;
                    } else {
                        // second occurrence of `(next b ...)`
                        coef_ang = iteration - coef_lin;
                        break;
                    }
                }
            }
            let frame = step_func.call_simple(&input, store, &lang, 0).unwrap();
            input = frame.output.clone();
            iteration += 1;
        }
        (coef_lin, coef_ang)
    }

    #[test]
    fn test_coeffs() {
        let store = Store::<pasta_curves::Fq>::default();
        assert_eq!(compute_coeffs(&store), (LIN_COEF, ANG_COEF));
    }

    #[test]
    fn test_fib_io_matches() {
        let store = Store::<pasta_curves::Fq>::default();
        let fib_9 = store.num_u64(34);
        let fib_10 = store.num_u64(55);
        let fib_11 = store.num_u64(89);
        assert_eq!(fib_9, lurk_fib(&store, 9));
        assert_eq!(fib_10, lurk_fib(&store, 10));
        assert_eq!(fib_11, lurk_fib(&store, 11));
    }
}
