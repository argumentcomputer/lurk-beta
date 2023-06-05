extern crate vergen;
use vergen::*;

fn main() {
    vergen(SHORT_SHA | COMMIT_DATE).unwrap();
}
