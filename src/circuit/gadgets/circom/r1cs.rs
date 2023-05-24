use ff::PrimeField;
use serde::{Deserialize, Serialize};

#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct CircomCircuit<Fr: PrimeField> {
    r1cs: R1CS<Fr>,
    witness: Option<Vec<Fr>>,
}

#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct R1CS<F: PrimeField> {
    pub(crate) num_inputs: usize,
    pub(crate) num_aux: usize,
    pub(crate) num_variables: usize,
    pub(crate) constraints: Vec<Constraint<F>>,
}

#[derive(Serialize, Deserialize)]
pub(crate) struct CircomInput {
    pub(crate) arg_in: Vec<String>,
}

pub(crate) type Constraint<F> = (Vec<(usize, F)>, Vec<(usize, F)>, Vec<(usize, F)>);
