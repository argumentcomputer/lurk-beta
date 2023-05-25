use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError};
use ff::PrimeField;
use num_bigint::BigInt;
use num_traits::Num;
use std::io::Error;
use std::process::Command;
use std::str;
use std::{
    env::current_dir,
    fs,
    path::{Path, PathBuf},
};

use crate::circuit::gadgets::circom::r1cs::{CircomInput, R1CS};
use crate::circuit::gadgets::circom::reader::{load_r1cs, load_witness_from_file};

fn generate_witness_from_wasm<Fr: PrimeField>(
    witness_wasm: &PathBuf,
    witness_input_json: &String,
    witness_output: &Path,
) -> Vec<Fr> {
    let root = current_dir().unwrap();
    let witness_generator_input = root.join("circom_input.json");
    fs::write(&witness_generator_input, witness_input_json).unwrap();

    let witness_js = Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/circuit/gadgets/circom/sha256/main_js/generate_witness.js"
    ));
    let output = Command::new("node")
        .arg(witness_js)
        .arg(witness_wasm)
        .arg(&witness_generator_input)
        .arg(witness_output)
        .output()
        .expect("failed to execute process");
    if !output.stdout.is_empty() || !output.stderr.is_empty() {
        print!("stdout: {}", str::from_utf8(&output.stdout).unwrap());
        print!("stderr: {}", str::from_utf8(&output.stderr).unwrap());
    }
    let _ = fs::remove_file(witness_generator_input);
    load_witness_from_file(witness_output)
}

#[allow(dead_code)]
pub fn sha256_circom<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input1: F,
    input2: F,
    p: PathBuf,
) -> Result<AllocatedNum<F>, SynthesisError> {

    let circuit_file = p.join("src/circuit/gadgets/circom/sha256/main.r1cs");
    let r1cs = load_r1cs(&circuit_file);

    let witness_generator_file = p.join("src/circuit/gadgets/circom/sha256/main_js/main.wasm");
    let hash_preimage = vec![input1, input2];
    let witness = generate_witness(hash_preimage, witness_generator_file)?;

    synthesize(cs, r1cs, Some(witness))
}

fn generate_witness<F: PrimeField>(
    hash_preimage: Vec<F>,
    witness_generator_file: PathBuf,
) -> Result<Vec<F>, Error> {
    let hash_preimage_hex = hash_preimage
        .iter()
        .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
        .collect::<Vec<String>>();
    let current_hash_preimage = hash_preimage_hex;

    let decimal_stringified_input: Vec<String> = current_hash_preimage
        .iter()
        .map(|x| BigInt::from_str_radix(x, 16).unwrap().to_str_radix(10))
        .collect();

    let input = CircomInput {
        arg_in: decimal_stringified_input,
    };

    let input_json = serde_json::to_string(&input).unwrap();

    let root = current_dir().unwrap();
    let witness_generator_output = root.join("circom_witness.wtns");

    let witness = generate_witness_from_wasm::<F>(
        &witness_generator_file,
        &input_json,
        &witness_generator_output,
    );

    Ok(witness)
}

/// Reference work is Nota-Scotia: https://github.com/nalinbhardwaj/Nova-Scotia
fn synthesize<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    r1cs: R1CS<F>,
    witness: Option<Vec<F>>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    //println!("witness: {:?}", witness);
    //println!("num_inputs: {:?}", r1cs.num_inputs);
    //println!("num_aux: {:?}", r1cs.num_aux);
    //println!("num_variables: {:?}", r1cs.num_variables);
    //println!("num constraints: {:?}", r1cs.constraints.len());

    let witness = &witness;

    let mut vars: Vec<AllocatedNum<F>> = vec![];

    for i in 1..r1cs.num_inputs {
        let f: F = {
            match witness {
                None => F::ONE,
                Some(w) => w[i],
            }
        };
        let v = AllocatedNum::alloc(cs.namespace(|| format!("public_{}", i)), || Ok(f))?;

        vars.push(v.clone());
    }
    for i in 0..r1cs.num_aux {
        // Private witness trace
        let f: F = {
            match witness {
                None => F::ONE,
                Some(w) => w[i + r1cs.num_inputs],
            }
        };

        let v = AllocatedNum::alloc(cs.namespace(|| format!("aux_{}", i)), || Ok(f))?;
        vars.push(v);
    }

    let output = vars[0].clone();

    let make_lc = |lc_data: Vec<(usize, F)>| {
        let res = lc_data.iter().fold(
            LinearCombination::<F>::zero(),
            |lc: LinearCombination<F>, (index, coeff)| {
                lc + if *index > 0 {
                    (*coeff, vars[*index - 1].get_variable())
                } else {
                    (*coeff, CS::one())
                }
            },
        );
        res
    };
    for (i, constraint) in r1cs.constraints.iter().enumerate() {
        cs.enforce(
            || format!("constraint {}", i),
            |_| make_lc(constraint.0.clone()),
            |_| make_lc(constraint.1.clone()),
            |_| make_lc(constraint.2.clone()),
        );
    }

    Ok(output)
}

#[cfg(test)]
mod tests {
    use std::env::current_dir;
    use pasta_curves::vesta::Scalar as Fr;

    use crate::circuit::gadgets::circom::sha256::sha256_circom;
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use bellperson::util_cs::Comparable;
    use bellperson::ConstraintSystem;

    #[test]
    fn sha256_circom_test() {
        // If file sha256/main.circom changes, run the following:
        // REMARK: the scalar field in Vesta curve is Pallas field.
        // Then the prime parameter must be pallas if you set Fr to vesta::Scalar.
        // circom main.circom --r1cs --wasm --sym --c --output . --prime pallas --json

        let mut root = current_dir().unwrap();
        let mut cs = TestConstraintSystem::<Fr>::new();

        let output = sha256_circom(
            &mut cs.namespace(|| "sha256_circom"),
            Fr::from(0),
            Fr::from(0),
            root,
        );

        let expected = "0x00000000008619b3767c057fdf8e6d99fde2680c5d8517eb06761c0878d40c40";
        assert!(output.is_ok());
        let output_num = output.unwrap();
        assert!(format!("{:?}", output_num.get_value().unwrap()) == expected);
        assert!(cs.is_satisfied());
        assert_eq!(30134, cs.num_constraints());
        assert_eq!(1, cs.num_inputs());
        assert_eq!(29822, cs.aux().len());
    }
}
