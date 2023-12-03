use std::{cell::RefCell, rc::Rc, sync::Arc, time::Duration};

use anyhow::anyhow;

use pasta_curves::pallas;

use lurk::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{eval::evaluate, multiframe::MultiFrame, pointers::Ptr, store::Store},
    proof::Prover,
    proof::{nova::NovaProver, RecursiveSNARKTrait},
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    state::State,
};

use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

fn fib<F: LurkField>(store: &Store<F>, state: Rc<RefCell<State>>, _a: u64) -> Ptr {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

    store.read(state, program).unwrap()
}

// The env output in the `fib_frame`th frame of the above, infinite Fibonacci computation will contain a binding of the
// nth Fibonacci number to `a`.
// means of computing it.]
fn fib_frame(n: usize) -> usize {
    11 + 16 * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}

#[derive(Clone, Debug, Copy)]
struct ProveParams {
    fib_n: usize,
    rc: usize,
}

fn rc_env() -> anyhow::Result<Vec<usize>> {
    std::env::var("LURK_RC")
        .map_err(|e| anyhow!("Reduction count env var isn't set: {e}"))
        .and_then(|rc| {
            let vec: anyhow::Result<Vec<usize>> = rc
                .split(',')
                .map(|rc| {
                    rc.parse::<usize>()
                        .map_err(|e| anyhow!("Failed to parse RC: {e}"))
                })
                .collect();
            vec
        })
}

fn fibonacci_prove(prove_params: ProveParams, state: &Rc<RefCell<State>>) {
    let limit = fib_limit(prove_params.fib_n, prove_params.rc);
    let lang_pallas = Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new();
    let lang_rc = Arc::new(lang_pallas.clone());

    // use cached public params
    let instance = Instance::new(
        prove_params.rc,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();

    let store = Store::default();

    let ptr = fib::<pasta_curves::Fq>(&store, state.clone(), prove_params.fib_n as u64);
    let prover = NovaProver::new(prove_params.rc, lang_rc.clone());

    let frames = &evaluate::<pasta_curves::Fq, Coproc<pasta_curves::Fq>>(None, ptr, &store, limit)
        .unwrap()
        .0;
    let (proof, z0, zi, num_steps) = tracing_texray::examine(tracing::info_span!("bang!"))
        .in_scope(|| prover.prove(&pp, frames, &store).unwrap());

    let res = proof.verify(&pp, &z0, &zi, num_steps).unwrap();
    assert!(res);
}

/// RUST_LOG=info LURK_RC=900 LURK_PERF=max-parallel-simple cargo run --release --example fibonacci --features "cuda"
fn main() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new().width(120));
    tracing::subscriber::set_global_default(subscriber).unwrap();

    let rcs = rc_env().unwrap_or_else(|_| vec![100]);
    let batch_sizes = [249];

    let state = State::init_lurk_state().rccell();

    for rc in rcs.iter() {
        for fib_n in batch_sizes.iter() {
            let prove_params = ProveParams {
                fib_n: *fib_n,
                rc: *rc,
            };
            fibonacci_prove(prove_params, &state);
        }
    }

    println!("success");
}
