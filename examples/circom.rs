//! # Circom Gadgets
//!
//! ## Setting up a Circom Gadget with Lurk
//!
//! First, in a separate directory from `lurk-rs`, clone the circomlib repo with the `Sha256_2` circuit.
//! ```
//! git clone git@github.com:iden3/circomlib.git && cd circomlib
//! ```
//! In the `circuits` folder, create a new file called `sha256_2.circom`.
//! ```
//! cd circuits && touch sha256.circom
//! ```
//! In this new file, reate the main component that simply calls the `Sha256_2` circuit.
//! ```
//! pragma circom 2.1.4;
//! 
//! include "circomlib/sha256/sha256_2.circom";
//! 
//! component main = Sha256_2();
//! ```
//! 
//! Now return to the `lurk-rs` directory and run the following commands
//! ```
//! cargo run --release -- circom --name sha256_2 <PATH_TO_CIRCOMLIB>/circuits
//! cargo run --release --example circom
//! ```
//!
//! This compiles the circom project and processes it for lurk to interface with.
//! The new `sha256_2` gadget is stored in `.lurk/circom/sha256_2/*`. To use the gadget, 
//! create a `CircomSha256` struct and implement the [CircomGadget] trait. Refer to the 
//! example code below. Finally, declare the sha256 coprocessor:
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

#[cfg(not(target_arch = "wasm32"))]
use lurk::coprocessor::circom::non_wasm::CircomCoprocessor;

use lurk::eval::{empty_sym_env, lang::Lang};
use lurk::field::LurkField;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::ptr::Ptr;
use lurk::public_parameters::{public_params, public_params_default_dir};
use lurk::store::Store;
use lurk::{Num, Symbol};
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
        "circom_sha25"
    }

    fn into_circom_input(self, _input: &[AllocatedPtr<F>]) -> Vec<(String, Vec<F>)> {
        // TODO: actually use the lurk inputs
        let arg_in = ("arg_in".into(), vec![F::ZERO, F::ZERO]);
        vec![arg_in]
    }

    fn simple_evaluate(&self, s: &mut Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        // TODO: actually use the lurk inputs
        let expected = Num::Scalar(
            F::from_str_vartime(
                "55165702627807990590530466439275329993482327026534454077267643456",
            )
            .unwrap(),
        );
        s.intern_num(expected)
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
    let store = &mut Store::<Fr>::new();
    let sym_str = Symbol::new(&[".circom_sha256_2"]); // two inputs
    let circom_sha256 = CircomSha256::new(0);
    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(
            sym_str.clone(),
            CircomCoprocessor::new(circom_sha256).into(),
        )],
    );

    let coproc_expr = format!("{}", sym_str);
    dbg!(coproc_expr.clone());

    let expr = format!("({coproc_expr})");
    let ptr = store.read(&expr).unwrap();

    let nova_prover = NovaProver::<Fr, Sha256Coproc<Fr>>::new(REDUCTION_COUNT, lang.clone());
    let lang_rc = Arc::new(lang);

    println!("Setting up public parameters...");

    let pp_start = Instant::now();
    let pp = public_params::<_, Sha256Coproc<Fr>>(
        REDUCTION_COUNT,
        lang_rc.clone(),
        &public_params_default_dir(),
    )
    .unwrap();
    let pp_end = pp_start.elapsed();

    println!("Public parameters took {:?}", pp_end);

    println!("Beginning proof step...");

    let proof_start = Instant::now();
    let (proof, z0, zi, num_steps) = nova_prover
        .evaluate_and_prove(&pp, ptr, empty_sym_env(store), store, 10000, lang_rc)
        .unwrap();
    let proof_end = proof_start.elapsed();

    println!("Proofs took {:?}", proof_end);

    println!("Verifying proof...");

    let verify_start = Instant::now();
    let res = proof.verify(&pp, num_steps, &z0, &zi).unwrap();
    let verify_end = verify_start.elapsed();

    println!("Verify took {:?}", verify_end);

    if res {
        println!(
            "Congratulations! You proved and verified a CIRCOM-SHA256 hash calculation in {:?} time!",
            pp_end + proof_end + verify_end
        );
    }
}
