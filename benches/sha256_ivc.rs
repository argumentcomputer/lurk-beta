use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::data::GlobalAllocations;
use lurk::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use lurk::coprocessor::{CoCircuit, Coprocessor};
use lurk::eval::{empty_sym_env, lang::Lang};
use lurk::field::LurkField;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::ptr::Ptr;
use lurk::public_parameters::with_public_params;
use lurk::state::user_sym;
use lurk::store::Store;
use lurk::tag::{ExprTag, Tag};
use lurk::Num;
use lurk_macros::Coproc;

use bellpepper::gadgets::multipack::pack_bits;
use bellpepper::gadgets::sha256::sha256;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use pasta_curves::pallas::Scalar as Fr;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const REDUCTION_COUNT: usize = 10;

fn sha256_expr<F: LurkField>(store: &mut Store<F>, x: Vec<F>) -> Ptr<F> {
    let program = format!(r#"
(letrec ((encode-1 (lambda (term) 
            (let ((type (car term))
                  (value (cdr term)))
                (if (eq 'sha256 type)
                    (.lurk.user.sha256x-64-zero-bytes value)
                    (if (eq 'lurk type)
                        (commit value)
                        (if (eq 'id type)
                            value))))))
      (encode (lambda (input)
                (if input
                    (cons 
                        (encode-1 (car input))
                        (encode (cdr input)))))))
  (encode '((sha256 {x:?}) (lurk . 5) (id . 15))))
"#);

    store.read(&program).unwrap()
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct Sha256Coprocessor<F: LurkField> {
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {
    fn arity(&self) -> usize {
        1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        _store: &Store<F>,
        input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let preimage_ptr = &input_exprs[0];

        let zero = Boolean::constant(false);

        let mut preimage_bits = preimage_ptr
            .tag()
            .to_bits_le_strict(&mut cs.namespace(|| "preimage_tag_bits"))?;
        let preimage_hash_bits = preimage_ptr
            .hash()
            .to_bits_le_strict(&mut cs.namespace(|| "preimage_hash_bits"))?;

        preimage_bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
        preimage_bits.extend(preimage_hash_bits);
        preimage_bits.push(zero); // need 256 bits (or some multiple of 8).
        preimage_bits.reverse();

        let mut digest_bits = sha256(cs.namespace(|| "digest_bits"), &preimage_bits)?;

        digest_bits.reverse();

        // Fine to lose the last <1 bit of precision.
        let digest_scalar = pack_bits(cs.namespace(|| "digest_scalar"), &digest_bits)?;
        let output_expr = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "output_expr"),
            ExprTag::Num.to_field(),
            digest_scalar,
        )?;
        Ok((output_expr, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        1
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let mut hasher = Sha256::new();

        let preimage_ptr = args[0];
        let preimage_zptr = s.hash_expr(&preimage_ptr).unwrap();
        let preimage_tag: F = preimage_zptr.tag().to_field();
        let preimage_hash = preimage_zptr.value();
        let mut input = [0u8; 64];
        input[..32].copy_from_slice(&preimage_tag.to_bytes());
        input[32..].copy_from_slice(&preimage_hash.to_bytes());
        input.reverse();

        hasher.update(input);
        let mut bytes = hasher.finalize();

        bytes.reverse();
        let l = bytes.len();
        // Discard the two most significant bits.
        bytes[l - 1] &= 0b00111111;

        let scalar = F::from_bytes(&bytes).unwrap();
        let result = Num::from_scalar(scalar);

        s.intern_num(result)
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

impl<F: LurkField> Sha256Coprocessor<F> {
    pub(crate) fn new(n: usize) -> Self {
        Self {
            n,
            _p: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
enum Sha256Coproc<F: LurkField> {
    SC(Sha256Coprocessor<F>),
}

/// Run the example in this file with
/// `cargo run --release --example sha256_ivc`
fn main() {
    pretty_env_logger::init();

    let input_size = 64;

    let store = &mut Store::<Fr>::new();
    let cproc_sym = user_sym(&format!("sha256x-{input_size}-zero-bytes"));

    let call = sha256_expr(store);

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(cproc_sym, Sha256Coprocessor::new(input_size).into())],
    );
    let lang_rc = Arc::new(lang.clone());

    let nova_prover = NovaProver::<Fr, Sha256Coproc<Fr>>::new(REDUCTION_COUNT, lang);

    println!("Setting up public parameters (rc = {REDUCTION_COUNT})...");

    let pp_start = Instant::now();

    // see the documentation on `with_public_params`
    with_public_params(REDUCTION_COUNT, lang_rc.clone(), |pp| {
        let pp_end = pp_start.elapsed();
        println!("Public parameters took {:?}", pp_end);

        println!("Beginning proof step...");
        let proof_start = Instant::now();
        let (proof, z0, zi, num_steps) = nova_prover
            .evaluate_and_prove(pp, call, empty_sym_env(store), store, 10000, lang_rc)
            .unwrap();
        let proof_end = proof_start.elapsed();

        println!("Proofs took {:?}", proof_end);

        println!("Verifying proof...");

        let verify_start = Instant::now();
        let res = proof.verify(pp, num_steps, &z0, &zi).unwrap();
        let verify_end = verify_start.elapsed();

        println!("Verify took {:?}", verify_end);

        if res {
            println!(
                "Congratulations! You proved and verified a SHA256 hash calculation in {:?} time!",
                pp_end + proof_end + verify_end
            );
        }
    })
    .unwrap();
}
