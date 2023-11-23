//! This example implements a CLI application that checks whether a proof claims
//! that a call (with a specific format explained below) reduces to `t` when
//! evaluated under an empty env.
//!
//! The call mentioned above is of the form
//! ```lisp
//! ((open <fn_hash>) (open <arg_hash1>) (open <arg_hash2>) ...)
//! ```
//!
//! Let's commit to a function that checks whether a number is 0:
//! ```text
//! user> (commit (lambda (x) (= x 0)))
//! [2 iterations] => (comm 0x12fd195019bdb66f20bd06792d25718b1e1e7a48c3e8cbe704d78b9e2a258f55)
//! ```
//! Let's also commit to the number 0:
//! ```text
//! user> (commit 0)
//! [2 iterations] => (comm 0x0fa797fb1ca00c0148d4dd316cb38aad581e07bb70b058043ef6e4083fbea38c)
//! ```
//! And this is the computation to be proved:
//! ```text
//! user>
//! ((open 0x12fd195019bdb66f20bd06792d25718b1e1e7a48c3e8cbe704d78b9e2a258f55)
//!  (open 0x0fa797fb1ca00c0148d4dd316cb38aad581e07bb70b058043ef6e4083fbea38c))
//! [11 iterations] => t
//! user> !(prove)
//! Claim hash: 0x2b99f19f3737380d2fe08704a63ae0cfbacf4b3e2213a6d5be2da4c10005d9a8
//! Proof key: "Nova_Pallas_10_2b99f19f3737380d2fe08704a63ae0cfbacf4b3e2213a6d5be2da4c10005d9a8"
//! ```
//!
//! Now we can check whether that proof claims that such call reduces to `t`:
//! ```bash
//! cargo run --example validate_call \
//!   Nova_Pallas_10_2b99f19f3737380d2fe08704a63ae0cfbacf4b3e2213a6d5be2da4c10005d9a8 \
//!   0x12fd195019bdb66f20bd06792d25718b1e1e7a48c3e8cbe704d78b9e2a258f55 \
//!   0x0fa797fb1ca00c0148d4dd316cb38aad581e07bb70b058043ef6e4083fbea38c
//! Proof claim matches expectation
//! ```
//! * The first argument is the proof key
//! * The second argument is the hash of the committed function
//! * The remaining arguments are the hashes of the commitments to the function
//!   arguments

use abomonation::Abomonation;
use anyhow::{anyhow, bail, Result};
use ff::PrimeField;
use lurk::{
    cli::{field_data::load, lurk_proof::LurkProof, paths::proof_path},
    coprocessor::Coprocessor,
    lem::{multiframe::MultiFrame, store::Store, Tag},
    proof::{nova::CurveCycleEquipped, MultiFrameTrait},
    state::initial_lurk_state,
    tag::ExprTag,
};
use nova::traits::Engine;
use serde::{de::DeserializeOwned, Serialize};

fn validate_call<
    'a,
    F: CurveCycleEquipped + DeserializeOwned,
    C: Coprocessor<F> + Serialize + DeserializeOwned + 'a,
    M: MultiFrameTrait<'a, F, C>,
>(
    proof_key: &str,
    fn_hash: &str,
    args_hashes: &[String],
) -> Result<bool>
where
    <F as PrimeField>::Repr: abomonation::Abomonation,
    <<<F as CurveCycleEquipped>::E2 as Engine>::Scalar as PrimeField>::Repr: Abomonation,
{
    // load first to error early if the proof file is not present
    // this example searches Lurk's default proof path, but a different one could be provided
    let proof = load::<LurkProof<'_, F, C, M>>(&proof_path(proof_key))?;

    let store = Store::<F>::default();

    // build the list that represents the desired call
    // ((open <fn_hash>) (open <arg_hash1>) (open <arg_hash2>) ...)
    let mut call_elts = Vec::with_capacity(1 + args_hashes.len());
    let open = store.intern_lurk_symbol("open");
    let mut parse_and_push_open_call = |hash_str| -> Result<()> {
        let hash_ptr = store.read_with_default_state(hash_str)?;
        if hash_ptr.tag() != &Tag::Expr(ExprTag::Num) {
            bail!(
                "Invalid data type. Expected a number but got {}",
                hash_ptr.fmt_to_string(&store, initial_lurk_state())
            )
        }
        let open_call = store.list(vec![open, hash_ptr]); // (open <hash>)
        call_elts.push(open_call);
        Ok(())
    };
    parse_and_push_open_call(fn_hash)?;
    for arg_hash in args_hashes {
        parse_and_push_open_call(arg_hash)?;
    }

    // claim `Ptr`s
    let call = store.list(call_elts);
    let t = store.intern_lurk_symbol("t");
    let nil = store.intern_nil();
    let outermost = store.cont_outermost();
    let terminal = store.cont_terminal();

    // claim `ZPtr`s
    let z_call = store.hash_ptr(&call);
    let z_t = store.hash_ptr(&t);
    let z_nil = store.hash_ptr(&nil);
    let z_outermost = store.hash_ptr(&outermost);
    let z_terminal = store.hash_ptr(&terminal);

    Ok(proof.matches(
        Some(&z_call),
        Some(&z_t),
        Some(&z_nil),
        Some(&z_nil),
        Some(&z_outermost),
        Some(&z_terminal),
    ))
}

fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<_>>();
    // proof key is the first argument
    let proof_key = args
        .get(1)
        .ok_or_else(|| anyhow!("Proof key not provided"))?;
    // function hash is the second argument
    let fn_hash = args
        .get(2)
        .ok_or_else(|| anyhow!("Function hash not provided"))?;
    // function arguments are the next ones
    let args_hashes = &args[3..];
    // this example is limited to the Pallas field and the `Coproc` coprocessor
    use lurk::eval::lang::Coproc;
    use pasta_curves::pallas::Scalar as Fr;
    if validate_call::<_, _, MultiFrame<'_, _, Coproc<Fr>>>(proof_key, fn_hash, args_hashes)? {
        println!("Proof claim matches expectation");
        Ok(())
    } else {
        bail!("Proof claim does not match expectation")
    }
}
