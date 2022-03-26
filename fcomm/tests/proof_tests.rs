use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::Write;
use std::process::Command;
use tempdir::TempDir;

use blstrs::{Bls12, Scalar};

use fcomm::{Function, Proof};
use lurk::store::Store;

fn fcomm_cmd() -> std::process::Command {
    Command::cargo_bin("fcomm").unwrap()
}

#[test]
fn test_bad_command() {
    let mut cmd = fcomm_cmd();

    cmd.arg("uiop");
    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("Unsupported command: UIOP"));
}

#[test]
fn test_eval_expression() {
    let mut cmd = fcomm_cmd();

    cmd.arg("eval")
        .arg("--expression")
        .arg("tests/data/expression.lurk");

    cmd.assert()
        .success()
        .stdout("[17 iterations] IO { expr: 34, env: NIL, cont: Terminal }\n");
}

fn test_prove_expression<T: AsRef<OsStr>>(mut cmd: Command, expression_path: T, proof_path: T) {
    cmd.arg("prove")
        .arg("--expression")
        .arg(expression_path)
        .arg("--proof")
        .arg(proof_path);

    cmd.assert().success();
}

fn test_open_commitment<T: AsRef<OsStr>>(
    mut cmd: Command,
    function_path: T,
    input_path: T,
    proof_path: T,
) {
    cmd.arg("open")
        .arg("--function")
        .arg(function_path)
        .arg("--input")
        .arg(input_path)
        .arg("--proof")
        .arg(proof_path);

    cmd.assert().success();
}

fn test_verify_expression_proof<T: AsRef<OsStr>>(mut cmd: Command, proof_path: T) {
    cmd.arg("verify").arg("--proof").arg(proof_path);

    cmd.assert().success().stdout("{\"verified\":true}");
}

fn test_verify_opening<T: AsRef<OsStr>>(mut cmd: Command, proof_path: T) {
    cmd.arg("verify").arg("--proof").arg(proof_path);

    cmd.assert().success().stdout("{\"verified\":true}");
}

#[test]
fn test_prove_and_verify_expression() {
    let expression = "(* 9 7)";
    let expected = "63";

    let tmp_dir = TempDir::new("tmp").unwrap();
    let proof_path = tmp_dir.path().join("proof.json");
    let expression_path = tmp_dir.path().join("expression.lurk");

    let mut expression_file = File::create(&expression_path).unwrap();
    write!(expression_file, "{}", expression).unwrap();

    {
        test_prove_expression(fcomm_cmd(), &expression_path, &proof_path);

        let proof_string = fs::read_to_string(&proof_path).unwrap();
        let proof: Proof<Bls12> = serde_json::from_str(&proof_string).unwrap();

        assert_eq!(
            proof
                .claim
                .evaluation()
                .expect("expected evaluation claim")
                .expr_out,
            expected
        );
    }

    test_verify_expression_proof(fcomm_cmd(), &proof_path);
}

fn commit<T: AsRef<OsStr>>(function_path: T, commitment_path: T) {
    let mut cmd = fcomm_cmd();

    cmd.arg("commit")
        .arg("--function")
        .arg(&function_path)
        .arg("--commitment")
        .arg(&commitment_path)
        .assert()
        .success();
}

#[test]
fn test_create_open_and_verify_functional_commitment() {
    let function_source = "(lambda (x) (+ x 3))";
    let function_input = "22";
    let expected_output = "25";

    let function = Function::<Scalar> {
        source: function_source.into(),
        secret: None,
        commitment: None,
    };

    let tmp_dir = TempDir::new("tmp").unwrap();
    let proof_path = tmp_dir.path().join("proof.json");
    let function_path = tmp_dir.path().join("function.json");
    let input_path = tmp_dir.path().join("input.lurk");
    let commitment_path = tmp_dir.path().join("commitment.json");

    let function_file = File::create(&function_path).unwrap();
    let mut input_file = File::create(&input_path).unwrap();

    serde_json::to_writer(&function_file, &function).unwrap();
    write!(input_file, "{}", function_input).unwrap();

    {
        commit(&function_path, &commitment_path);

        test_open_commitment(fcomm_cmd(), &function_path, &input_path, &proof_path);

        let proof_string = fs::read_to_string(&proof_path).unwrap();
        let proof: Proof<Bls12> = serde_json::from_str(&proof_string).unwrap();
        let opening = proof.claim.opening().expect("expected opening claim");

        assert_eq!(function_input, opening.input);
        assert_eq!(expected_output, opening.output);
    }

    test_verify_opening(fcomm_cmd(), &proof_path);
}

fn test_create_open_and_verify_higher_order_functional_commitment_aux(
    function_source: &str,
    function_input: &str,
    expected_output: &str,
) {
    use lurk::writer::Write;

    let function = Function::<Scalar> {
        source: function_source.into(),
        secret: None,
        commitment: None,
    };

    let tmp_dir = TempDir::new("tmp").unwrap();
    let proof_path = tmp_dir.path().join("proof.json");
    let function_path = tmp_dir.path().join("function.json");
    let input_path = tmp_dir.path().join("input.lurk");
    let commitment_path = tmp_dir.path().join("commitment.json");

    let function_file = File::create(&function_path).unwrap();
    let mut input_file = File::create(&input_path).unwrap();

    serde_json::to_writer(&function_file, &function).unwrap();
    write!(input_file, "{}", function_input).unwrap();

    {
        commit(&function_path, &commitment_path);

        test_open_commitment(fcomm_cmd(), &function_path, &input_path, &proof_path);

        let proof_string = fs::read_to_string(&proof_path).unwrap();
        let proof: Proof<Bls12> = serde_json::from_str(&proof_string).unwrap();
        let opening = proof.claim.opening().expect("expected opening claim");

        let mut store = Store::<Scalar>::default();

        let input = store.read(function_input).unwrap();
        let canonical_input = input.fmt_to_string(&store);

        dbg!(&canonical_input, &opening.input);
        dbg!(&expected_output, &opening.output);
        assert_eq!(canonical_input, opening.input);
        assert_eq!(expected_output, opening.output);
    }

    test_verify_opening(fcomm_cmd(), &proof_path);
}

#[test]
fn test_create_open_and_verify_higher_order_functional_commitment() {
    let function_source = "(lambda (f) (+ (f 3) 1))";
    let function_input = "(lambda (x) (* x 5))";
    let expected_output = "16";
    test_create_open_and_verify_higher_order_functional_commitment_aux(
        function_source,
        function_input,
        expected_output,
    );
}

#[test]
fn test_create_open_and_verify_complicated_higher_order_functional_commitment1() {
    let function_source = "(let ((nums '(1 2 3 4 5))) (lambda (f) (f nums)))";
    let function_input = "(letrec ((sum-aux (lambda (acc nums)
                                              (if nums
                                                (sum-aux (+ acc (car nums)) (cdr nums))
                                                acc)))
                                   (sum (sum-aux 0)))
                             (lambda (nums)
                               (sum nums)))";
    let expected_output = "15";

    test_create_open_and_verify_higher_order_functional_commitment_aux(
        function_source,
        function_input,
        expected_output,
    );
}

#[test]
#[ignore]
// FIXME: This fails to verify, which seems to be a circuit bug.
fn test_create_open_and_verify_complicated_higher_order_functional_commitment2() {
    let function_source = "(letrec ((secret-data '((joe 4 3) (bill 10 2 3) (jane 8 7 6 10) (carol 3 5 8))) (filter (lambda (data predicate) (if data (if (predicate (cdr (car data))) (cons (car data) (filter (cdr data) predicate)) (filter (cdr data) predicate))))) (f (lambda (predicate) (car (car (filter secret-data predicate)))))) f)";

    let function_input = "(letrec ((sum-aux (lambda (acc nums)
                                              (if nums
                                                (sum-aux (+ acc (car nums)) (cdr nums))
                                                acc)))
                                   (sum (sum-aux 0)))
                             (lambda (nums)
                               (= (sum nums) 15)))";
    let expected_output = "BILL";

    test_create_open_and_verify_higher_order_functional_commitment_aux(
        function_source,
        function_input,
        expected_output,
    );
}
