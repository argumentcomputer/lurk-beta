use std::path::Path;
use std::fs::File;
use std::convert::TryFrom;
use std::io::{self, BufReader, BufWriter};
use lurk::{
    field::LurkField,
    proof::nova::PublicParams,
    store::{ScalarPointer, ScalarPtr, Store},
};
use pasta_curves::pallas;
use serde::{Deserialize, Serialize};

pub use crate::error::VerifyError;

pub mod error;

// TODO:
// - Test the proof can be verified after a serialization roundtrip
// - Commit changes
// - Pull in changes from main
// - Check the Wasm build works on laptop
// - Open a WIP PR, message Chhi'med with questions
// - Update fcomm to reflect new proof ScalarPtr structure
// - Should we include public parameters in the LurkProof?
// - Are the env and cont ScalarPtrs needed to verify a Nova proof?

pub const DEFAULT_REDUCTION_COUNT: ReductionCount = ReductionCount::One;

pub type S1 = pallas::Scalar;

#[derive(Debug, Serialize, Deserialize)]
pub struct VerificationResult {
    pub verified: bool,
}

impl VerificationResult {
    fn new(verified: bool) -> Self {
        Self { verified }
    }
}

// Number of circuit reductions per step, equivalent to `chunk_frame_count`
#[derive(Clone, Copy, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReductionCount {
    One,
    Five,
    Ten,
}

impl TryFrom<usize> for ReductionCount {
    type Error = String;

    fn try_from(count: usize) -> Result<Self, String> {
        match count {
            1 => Ok(ReductionCount::One),
            5 => Ok(ReductionCount::Five),
            10 => Ok(ReductionCount::Ten),
            c => Err(format!("Unsupported Reduction Count: {c}")),
        }
    }
}
impl ReductionCount {
    pub fn count(&self) -> usize {
        match self {
            Self::One => 1,
            Self::Five => 5,
            Self::Ten => 10,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct LurkProof<'a, F: LurkField> {
    #[serde(bound(
        serialize = "Claim<F>: Serialize",
        deserialize = "Claim<F>: Deserialize<'de>"
    ))]
    pub claim: Option<Claim<F>>,
    pub public_inputs: Vec<S1>,
    pub public_outputs: Vec<S1>,
    #[serde(bound(
        serialize = "lurk::proof::nova::Proof<'a>: Serialize",
        deserialize = "lurk::proof::nova::Proof<'a>: Deserialize<'de>"
    ))]
    pub proof: lurk::proof::nova::Proof<'a>,
    pub num_steps: usize,
    pub reduction_count: ReductionCount,
}

// Pair of input and expected output, so the verifier can check that
// they match the scalar public inputs and outputs
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Claim<F: LurkField> {
    Text(String, String),
    // TODO: Use syntax AST once implemented with LDON refactor
    //Syntax(Syn, Syn),
    ScalarPtr(ScalarPtr<F>, ScalarPtr<F>),
    // TODO
    //#[serde(bound(
    //    serialize = "Opening<F>: Serialize",
    //    deserialize = "Opening<F>: Deserialize<'de>"
    //))]
    // Opening(Opening<F>),
}

impl<'a> LurkProof<'a, S1> {
    pub fn verify(&self, pp: &PublicParams) -> Result<VerificationResult, VerifyError> {
        // Check if the stored input and output exprs are the same as the verifier expects
        if let Some(claim) = &self.claim {
            self.verify_claim(&claim)?;
        }
        let verified = self
            .proof
            .verify(
                pp,
                self.num_steps,
                self.public_inputs.clone(),
                &self.public_outputs,
            )
            .expect("error verifying");

        let result = VerificationResult::new(verified);

        Ok(result)
    }

    pub fn verify_claim(&self, claim: &Claim<S1>) -> Result<(), VerifyError> {
        let proof_exprs = (
            ScalarPtr::from_parts(self.public_inputs[0], self.public_inputs[1]),
            ScalarPtr::from_parts(self.public_outputs[0], self.public_outputs[1]),
        );
        let verify_exprs = match claim {
            Claim::Text(input, output) => {
                (string_to_scalar_ptr(input)?, string_to_scalar_ptr(output)?)
            }
            //Claim::Syntax(syn) => todo!(),
            Claim::ScalarPtr(scalar_input, scalar_output) => (*scalar_input, *scalar_output),
        };
        if proof_exprs != verify_exprs {
            return Err(VerifyError::Verification(
                "mismatched public inputs/outputs".into(),
            ));
        }
        Ok(())
    }

    pub fn write_to_path<P: AsRef<Path>>(&self, path: P) {
        let file = File::create(path).expect("failed to create file");
        let writer = BufWriter::new(&file);

        serde_json::to_writer(writer, &self).expect("failed to write file");
    }

    pub fn read_from_path<P: AsRef<Path>>(path: P) -> Result<Self, VerifyError> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        Ok(serde_json::from_reader(reader)?)
    }

    pub fn read_from_stdin() -> Result<Self, VerifyError> {
        let reader = BufReader::new(io::stdin());
        Ok(serde_json::from_reader(reader).expect("failed to read from stdin"))
    }

}

// TODO: Ignoring env and cont for simplicity, are they necessary?
// TODO: Refactor to parse into Syn once LDON is implemented
// Helper function to get a ScalarPtr from some input string
pub fn string_to_scalar_ptr(lurk_string: &str) -> Result<ScalarPtr<S1>, VerifyError> {
    let mut s = Store::<S1>::default();

    let ptr = s
        .read(&lurk_string)?;
        //.map_err(|_| VerifyError::Verification("failed to read expr".into()))?;

    s.get_expr_hash(&ptr)
        .ok_or(VerifyError::Verification("no such scalar ptr".into()))
}



#[cfg(test)]
mod tests {
    

    use lurk::{
        field::LurkField,
        proof::{
            nova::{self, public_params, NovaProver},
            Prover,
        },
        store::{Ptr, Store},
    };
    use serde::{Deserialize, Serialize};
    use tempdir::TempDir;

    use crate::{Error, LurkProof, S1, Claim};

    // Get proof from supplied path or else from stdin.
    //fn proof<'a, P: AsRef<Path>, F: LurkField>(
    //    proof_path: Option<P>,
    //) -> Result<LurkProof<'a, F>, Error>
    //where
    //    F: Serialize + for<'de> Deserialize<'de>,
    //{
    //    match proof_path {
    //        Some(path) => LurkProof::read_from_path(path),
    //        None => LurkProof::read_from_stdin(),
    //    }
    //}

    //fn read_from_path<P: AsRef<Path>, F: LurkField + Serialize>(
    //    store: &mut Store<F>,
    //    path: P,
    //) -> Result<Ptr<F>, Error> {
    //    let path = env::current_dir()?.join(path);
    //    let input = read_to_string(path)?;
    //    let src = store.read(&input).unwrap();

    //    Ok(src)
    //}

    #[test]
    fn proof_roundtrip() {
        let mut s = Store::<S1>::default();

        let input = "(+ 1 1)";
        let ptr = s.read(input).unwrap();
        let limit = 10000;
        let reduction_count = 1;
        let prover = NovaProver::<S1>::new(reduction_count);
        let pp = public_params(reduction_count);

        let fcomm_proof =
            fcomm::Proof::eval_and_prove(&mut s, ptr, limit, false, &prover, &pp).unwrap();

        let claim = match fcomm_proof.claim {
            fcomm::Claim::Evaluation(e) => Some(Claim::<S1>::Text(e.expr, e.expr_out)),
            _ => todo!(),
        };
        // Create Lurk proof
        let lurk_proof = LurkProof {
            claim,
            public_inputs: fcomm_proof.public_inputs,
            public_outputs: fcomm_proof.public_outputs,
            proof: fcomm_proof.proof,
            num_steps: fcomm_proof.num_steps,
        };

        let tmp_dir = TempDir::new("tmp").unwrap();
        let proof_path = tmp_dir.path().join("./proof.json");
        // Write Lurk proof to disk
        lurk_proof.write_to_path(proof_path);
        // Read Lurk proof from disk
        let lurk_proof = LurkProof::<S1>::read_from_path(proof_path);

        // Verify Lurk proof
        let res = lurk_proof.verify(&pp);
        assert!(res.is_ok());

        // Print successful verification (optional)
        // serde_json::to_writer(io::stdout(), &res)?;
    }
}
