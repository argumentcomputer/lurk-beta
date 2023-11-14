//! # Circom Gadgets
//!
//! ## Setting up a Circom Gadget with Lurk
//!
//! First, in a separate directory from `lurk-rs`, clone the circomlib repo with the `Sha256_2` circuit.
//! ```
//! git clone git@github.com:iden3/circomlib.git && cd circomlib
//! ```
//!
//! Now return to the `lurk-rs` directory and run the following commands
//! ```
//! cargo run --release -- circom --name sha256_2_test <PATH_TO_CIRCOMLIB>/test/circuits/
//! cargo run --release --example circom
//! ```
//!
//! This compiles the circom project and processes it for lurk to interface with.
//! The new `sha256_2_test` gadget is stored in `<CIRCOM_DIR>/sha256_2_test/*`.
//! To use the gadget, create a [CircomSha256] struct and implement the [CircomGadget] trait.
//! Refer to the example code below. Finally, declare the sha256 coprocessor:
//!
//! ```rust
//! #[derive(Clone, Debug, Coproc)]
//! enum Sha256Coproc<F: LurkField> {
//!    SC(CircomCoprocessor<F, CircomSha256<F>>),
//! }
//! ```
//!
//! Hooray! Now we can use a [CircomSha256] coprocessor just like a normal one.

use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::circom::CircomGadget;
use lurk::circuit::gadgets::pointer::AllocatedPtr;
use lurk::lem::multiframe::MultiFrame;

#[cfg(not(target_arch = "wasm32"))]
use lurk::coprocessor::circom::non_wasm::CircomCoprocessor;

use lurk::eval::lang::Lang;
use lurk::field::LurkField;
use lurk::lem::{pointers::Ptr, store::Store};
use lurk::proof::{nova::NovaProver, Prover};
use lurk::public_parameters::instance::{Instance, Kind};
use lurk::public_parameters::public_params;
use lurk::Symbol;
use lurk_macros::Coproc;
use pasta_curves::pallas::Scalar as Fr;

const REDUCTION_COUNT: usize = 1;

#[derive(Debug, Clone)]
pub struct CircomSha256<F: LurkField> {
    _n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CircomSha256<F> {
    fn new(n: usize) -> Self {
        CircomSha256 {
            _n: n,
            _p: PhantomData,
        }
    }
}

impl<F: LurkField> CircomGadget<F> for CircomSha256<F> {
    fn name(&self) -> &str {
        "sha256_2_test"
    }

    fn into_circom_input(self, _input: &[AllocatedPtr<F>]) -> Vec<(String, Vec<F>)> {
        // TODO: actually use the lurk inputs
        let a = ("a".into(), vec![F::ZERO]);
        let b = ("b".into(), vec![F::ZERO]);
        vec![a, b]
    }

    fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        // TODO: actually use the lurk inputs
        Ptr::num(
            F::from_str_vartime(
                "55165702627807990590530466439275329993482327026534454077267643456",
            )
            .unwrap(),
        )
    }
}

#[derive(Clone, Debug, Coproc)]
enum Sha256Coproc<F: LurkField> {
    SC(CircomCoprocessor<F, CircomSha256<F>>),
}

/// Run the example in this file with
/// `cargo run --release -- circom --name sha256_2 examples/sha256/`
/// `cargo run --release --example circom`
fn main() {
    let store = &Store::<Fr>::default();
    let sym_str = Symbol::new(&[".circom_sha256_2"], false); // two inputs
    let circom_sha256: CircomSha256<Fr> = CircomSha256::new(0);
    let mut lang = Lang::<Fr, Sha256Coproc<Fr>>::new();
    lang.add_coprocessor(sym_str, CircomCoprocessor::new(circom_sha256));

    let expr = "(.circom_sha256_2)".to_string();
    let ptr = store.read_with_default_state(&expr).unwrap();

    let nova_prover = NovaProver::<Fr, Sha256Coproc<Fr>, MultiFrame<'_, _, _>>::new(
        REDUCTION_COUNT,
        lang.clone(),
    );
    let lang_rc = Arc::new(lang);

    println!("Setting up public parameters...");

    let pp_start = Instant::now();
    let instance = Instance::new(
        REDUCTION_COUNT,
        lang_rc.clone(),
        true,
        Kind::NovaPublicParams,
    );
    let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();
    let pp_end = pp_start.elapsed();

    println!("Public parameters took {pp_end:?}");

    println!("Beginning proof step...");

    let proof_start = Instant::now();
    let (proof, z0, zi, num_steps) = nova_prover
        .evaluate_and_prove(&pp, ptr, store.intern_nil(), store, 10000, &lang_rc)
        .unwrap();
    let proof_end = proof_start.elapsed();

    println!("Proofs took {proof_end:?}");

    println!("Verifying proof...");

    let verify_start = Instant::now();
    let res = proof.verify(&pp, num_steps, &z0, &zi).unwrap();
    let verify_end = verify_start.elapsed();

    println!("Verify took {verify_end:?}");

    if res {
        println!(
            "Congratulations! You proved and verified a CIRCOM-SHA256 hash calculation in {:?} time!",
            pp_end + proof_end + verify_end
        );
    }
}
