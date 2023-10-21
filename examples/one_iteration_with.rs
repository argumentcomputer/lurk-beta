use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::circuit_frame::MultiFrame;
use lurk::eval::empty_sym_env;
use lurk::eval::lang::{Coproc, Lang};
use lurk::field::LurkField;
use lurk::proof::nova::NovaProver;
use lurk::proof::Prover;
use lurk::ptr::Ptr;
use lurk::public_parameters::instance::{Instance, Kind};
use lurk::public_parameters::{public_params_default_dir, with_public_params};
use lurk::store::Store;
use pasta_curves::pallas::Scalar as Fr;

use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

fn fib_expr<F: LurkField>(store: &Store<F>) -> Ptr<F> {
    let program = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

    store.read(program).unwrap()
}

fn lurk_fib(store: &Store<Fr>, rc: usize) {
    let limit = 2 * rc;
    let fib_expr = fib_expr(store);

    let lang = Lang::<Fr, Coproc<Fr>>::new();
    let lang_rc = Arc::new(lang.clone());
    let nova_prover = NovaProver::<Fr, _, MultiFrame<'_, _, Coproc<Fr>>>::new(rc, lang);

    // see the documentation on `with_public_params`
    let pp_start = Instant::now();
    let instance = Instance::new(rc, lang_rc.clone(), true, Kind::NovaPublicParams);
    with_public_params(&instance, &public_params_default_dir(), |pp| {
        let pp_end = pp_start.elapsed();
        println!("pp took: {:?}; beginning proof... (rc = {})", pp_end, rc);

        let (proof, z0, zi, num_steps) = tracing_texray::examine(tracing::info_span!("bang!"))
            .in_scope(|| {
                nova_prover
                    .evaluate_and_prove(pp, fib_expr, empty_sym_env(store), store, limit, &lang_rc)
                    .unwrap()
            });

        let res = proof.verify(pp, num_steps, &z0, &zi).unwrap();

        if res {
            println!("Congratulations! You proved and verified a SHA256 hash calculation!");
        }
    })
    .unwrap();
}

/// Run the example in this file with
/// `RUST_LOG=info cargo run --release --example one_iteration`
fn main() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new().width(120));
    tracing::subscriber::set_global_default(subscriber).unwrap();

    let store = &Store::<Fr>::new();

    for rc in [10, 50, 100, 200, 300, 400, 500, 600, 800, 1000] {
        lurk_fib(store, rc);
    }
}
