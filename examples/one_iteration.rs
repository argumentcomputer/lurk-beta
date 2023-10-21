use std::sync::Arc;
use std::thread::sleep;
use std::time::{Instant, Duration};

use lurk::circuit::circuit_frame::MultiFrame;
use lurk::eval::empty_sym_env;
use lurk::eval::lang::{Coproc, Lang};
use lurk::field::LurkField;
use lurk::proof::nova::NovaProver;
use lurk::proof::Prover;
use lurk::ptr::Ptr;
use lurk::public_parameters::instance::{Instance, Kind};
use lurk::public_parameters::{public_params_default_dir, nova_public_params, public_params};
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

fn lurk_fib(store: &Store<Fr>, rc: usize, fresh: bool) {
    let limit = 6 * rc;
    let fib_expr = fib_expr(store);

    let lang = Lang::<Fr, Coproc<Fr>>::new();
    let lang_rc = Arc::new(lang.clone());
    let nova_prover = NovaProver::<Fr, _, MultiFrame<'_, _, Coproc<Fr>>>::new(rc, lang);

    // see the documentation on `with_public_params`
    tracing_texray::examine(tracing::info_span!("bang!")).in_scope(|| {
        let pp_start = Instant::now();
        let pp = if fresh {
            let pp = lurk::proof::nova::public_params(rc, lang_rc.clone());
            Arc::new(pp)
        } else {
            let instance = Instance::new(rc, lang_rc.clone(), true, Kind::NovaPublicParams);
            public_params(&instance, &public_params_default_dir()).unwrap()
        };
        let pp_end = pp_start.elapsed();

        println!("pp took {:?}; beginning proof... (rc = {})", pp_end, rc);

        let (proof, z0, zi, num_steps) = nova_prover
            .evaluate_and_prove(&pp, fib_expr, empty_sym_env(store), store, limit, &lang_rc)
            .unwrap();

        let res: bool = proof.verify(&pp, num_steps, &z0, &zi).unwrap();
        assert!(res);
    });
}

/// Run the example in this file with
/// `RUST_LOG=info cargo run --release --example one_iteration -- true`
fn main() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new().width(600));
    tracing::subscriber::set_global_default(subscriber).unwrap();

    // let args = std::env::args().collect::<Vec<_>>();
    // let fresh: bool = args[1].parse().unwrap();

    let store = &Store::<Fr>::new();

    for iter in 0..5 {
        println!("iter: {iter}");
        lurk_fib(store, 900, true);
        sleep(Duration::from_secs(5));
    }

    for iter in 0..5 {
        println!("iter: {iter}");
        lurk_fib(store, 900, false);
        sleep(Duration::from_secs(5));
    }
}
