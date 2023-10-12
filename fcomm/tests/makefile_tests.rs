use std::env;
use std::path::PathBuf;
use std::process::Command;

#[ignore]
#[test]
fn test_make_fcomm_examples() {
    // Get the current working directory
    let mut current_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    // Find the examples directory
    current_dir.push("examples");
    let examples_dir = current_dir.as_path();
    assert!(
        examples_dir.exists() && examples_dir.is_dir(),
        "Failed to find the fcomm examples directory"
    );

    // Make clean
    let make_clean_output = Command::new("make")
        .arg("clean")
        .current_dir(examples_dir)
        .output()
        .expect("Failed to run the make command, is make installed?");

    assert!(
        make_clean_output.status.success(),
        "Make command exited with an error: {}",
        String::from_utf8_lossy(&make_clean_output.stderr)
    );

    // Run the make command in the examples directory
    let cpus = num_cpus::get();

    let make_output = Command::new("make")
        .current_dir(examples_dir)
        .arg(format!("-j{cpus}"))
        .output()
        .expect("Failed to run the make command, is make installed?");

    // Check the exit status
    assert!(
        make_output.status.success(),
        "Make command exited with an error: {}",
        String::from_utf8_lossy(&make_output.stderr)
    );
}
