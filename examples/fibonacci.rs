use lurk::{
    field::LurkField,
    lem::{eval::evaluate_simple, pointers::Ptr, store::Store},
    {eval::lang::Coproc, state::State},
};
use pasta_curves::Fq;

fn fib_expr<F: LurkField>(store: &Store<F>) -> Ptr<F> {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

    store.read_with_default_state(program).unwrap()
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

fn lurk_fib(store: &Store<Fq>, n: usize, _rc: usize) -> Ptr<Fq> {
    let frame_idx = fib_frame(n);
    // let limit = fib_limit(n, rc);
    let limit = frame_idx;
    let fib_expr = fib_expr(store);

    let (output, ..) = evaluate_simple::<Fq, Coproc<Fq>>(None, fib_expr, store, limit).unwrap();

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

fn main() {
    let store = &Store::<Fq>::default();
    let n: usize = std::env::args().collect::<Vec<_>>()[1].parse().unwrap();
    let state = State::init_lurk_state();

    let fib = lurk_fib(store, n, 100);

    println!("Fib({n}) = {}", fib.fmt_to_string(store, &state));
}
