use lurk::field::LurkField;
use lurk::ptr::Ptr;
use lurk::store::Store;
use lurk::writer::Write;
use lurk::{
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
        Evaluator,
    },
    state::State,
};
use pasta_curves::pallas::Scalar;

fn fib_expr<F: LurkField>(store: &mut Store<F>) -> Ptr<F> {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

    store.read(program).unwrap()
}

// The env output in the `fib_frame`th frame of the above, infinite Fibonacci computation contains a binding of the
// nth Fibonacci number to `a`.
fn fib_frame(n: usize) -> usize {
    11 + 16 * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
#[allow(dead_code)]
fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}

fn lurk_fib(store: &mut Store<Scalar>, n: usize, _rc: usize) -> Ptr<Scalar> {
    let lang = Lang::<Scalar, Coproc<Scalar>>::new();
    let frame_idx = fib_frame(n);
    // let limit = fib_limit(n, rc);
    let limit = frame_idx;
    let fib_expr = fib_expr(store);

    let frames = Evaluator::new(fib_expr, empty_sym_env(store), store, limit, &lang)
        .get_frames()
        .unwrap();

    let target_frame = frames.last().unwrap();

    let target_env = target_frame.output.env;

    // The result is the value of the second binding (of `A`), in the target env.
    // See relevant excerpt of execution trace below:
    //
    // INFO  lurk::eval > Frame: 11
    // Expr: (NEXT B (+ A B))
    // Env: ((B . 1) (A . 0) ((NEXT . <FUNCTION (A) (LAMBDA (B) (NEXT B (+ A B)))>)))
    // Cont: Tail{ saved_env: (((NEXT . <FUNCTION (A) (LAMBDA (B) (NEXT B (+ A B)))>))), continuation: LetRec{var: FIB,
    //       saved_env: (((NEXT . <FUNCTION (A) (LAMBDA (B) (NEXT B (+ A B)))>))), body: (FIB), continuation: Tail{ saved_env:
    //       NIL, continuation: Outermost } } }

    let rest_bindings = store.cdr(&target_env).unwrap();
    let second_binding = store.car(&rest_bindings).unwrap();
    store.cdr(&second_binding).unwrap()
}

fn main() {
    let store = &mut Store::<Scalar>::new();
    let n: usize = std::env::args().collect::<Vec<_>>()[1].parse().unwrap();
    let state = State::init_lurk_state();

    let fib = lurk_fib(store, n, 100);

    println!("Fib({n}) = {}", fib.fmt_to_string(store, &state));
}
