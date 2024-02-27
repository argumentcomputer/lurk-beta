use std::sync::Arc;

use anyhow::anyhow;

use halo2curves::bn256::Fr as Bn;

use lurk::{
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{eval::evaluate, pointers::Ptr, store::Store},
    proof::{nova::NovaProver, RecursiveSNARKTrait},
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
};

use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

pub(crate) fn fib_expr<F: LurkField>(store: &Store<F>) -> Ptr {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
         (fib (next 0 1)))
  (fib))
"#;

    store.read_with_default_state(program).unwrap()
}

const LIN_COEF: usize = 7;
const ANG_COEF: usize = 7;

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

fn fibonacci_prove(prove_params: ProveParams) {
    let limit = fib_limit(prove_params.fib_n, prove_params.rc);
    let lang = Lang::<Bn>::new();
    let lang_rc = Arc::new(lang.clone());

    // use cached public params
    let instance = Instance::new(
        prove_params.rc,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_params(&instance).unwrap();

    let store = Store::default();

    let ptr = fib_expr::<Bn>(&store);
    let prover = NovaProver::new(prove_params.rc, lang_rc.clone());

    let frames = &evaluate::<Bn, Coproc<Bn>>(None, ptr, &store, limit).unwrap();
    let _ = tracing_texray::examine(tracing::info_span!("bang!"))
        .in_scope(|| prover.prove_from_frames(&pp, &frames, &store).unwrap());
    let (proof, z0, zi, _num_steps) = tracing_texray::examine(tracing::info_span!("bang!"))
        .in_scope(|| prover.prove_from_frames(&pp, &frames, &store).unwrap());

    let res = proof.verify(&pp, &z0, &zi).unwrap();
    assert!(res);
}

/// RUST_LOG=info LURK_RC=900 LURK_PERF=max-parallel-simple cargo run --release --example fibonacci --features "cuda"
fn main() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new().width(120));
    tracing::subscriber::set_global_default(subscriber).unwrap();

    let rcs = rc_env().unwrap_or_else(|_| vec![900]);
    let batch_sizes = [300];

    for rc in rcs.iter() {
        for fib_n in batch_sizes.iter() {
            let prove_params = ProveParams {
                fib_n: *fib_n,
                rc: *rc,
            };
            fibonacci_prove(prove_params);
        }
    }

    println!("success");
}