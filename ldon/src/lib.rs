#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

extern crate lurk_ff;

pub mod expr;
pub mod hash;
pub mod parser;
pub mod ptr;
pub mod store;
pub mod syntax;

#[cfg(test)]
pub mod test {
    use quickcheck::Gen;
    use rand::Rng;

    // This is a useful testing utility for generating Arbitrary instances of
    // enums, by providing generators for each variant, plus a frequency weight
    // for how often to choose that variant. It's included in lib::test to make
    // it easier to import in the test modules of specific submodules.
    pub fn frequency<T, F: Fn(&mut Gen) -> T>(g: &mut Gen, gens: Vec<(i64, F)>) -> T {
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
            } else {
                weight -= gen.0;
            }
        }
        panic!("Calculation error for weight = {}", weight);
    }
}
