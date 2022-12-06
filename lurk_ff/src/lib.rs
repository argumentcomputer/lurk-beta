#[cfg(any(test, feature = "test-utils"))]
extern crate quickcheck;
#[cfg(any(test, feature = "test-utils"))]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub mod field;
pub mod tag;

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

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use quickcheck::Gen;
  use rand::Rng;

  // This is a useful testing utility for generating Arbitrary instances of
  // enums, by providing generators for each variant, plus a frequency weight
  // for how often to choose that variant. It's included in lib::test to make
  // it easier to import in the test modules of specific submodules.
  pub fn frequency<T, F: Fn(&mut Gen) -> T>(
    g: &mut Gen,
    gens: Vec<(i64, F)>,
  ) -> T {
    if gens.iter().any(|(v, _)| *v < 0) {
      panic!("Negative weight");
    }
    let sum: i64 = gens.iter().map(|x| x.0).sum();
    let mut rng = rand::thread_rng();
    let mut weight: i64 = rng.gen_range(1..=sum);
    // let mut weight: i64 = g.rng.gen_range(1, sum);
    for gen in gens {
      if weight - gen.0 <= 0 {
        return gen.1(g);
      }
      else {
        weight -= gen.0;
      }
    }
    panic!("Calculation error for weight = {}", weight);
  }
}

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
