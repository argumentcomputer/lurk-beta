#[cfg(any(test, feature = "test-utils"))]
extern crate quickcheck;
#[cfg(any(test, feature = "test-utils"))]
#[allow(unused_imports)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

extern crate lurk_ff;

pub mod cont;
pub mod expr;
pub mod hash;
pub mod parser;
pub mod ptr;
pub mod serde_f;
pub mod store;
pub mod syntax;

#[cfg(all(test, not(feature = "test-utils")))]
pub mod test {
  // This shouldn't ever run since "test-utils" is set in Cargo
  // dev-dependencies, but just in case someone disables it we want to avoid
  // test-suite false positives
  #[test]
  fn fail_without_test_utils_feature() {
    println!(
      "Test suite requires \"test-utils\" feature. 
      Please run `cargo test --features=test-utils`, or `cargo test \
       --all-features`, or add it to your dev-dependencies
      "
    );
    assert!(false)
  }
}
