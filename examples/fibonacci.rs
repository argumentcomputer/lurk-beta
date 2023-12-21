use pasta_curves::Fq;

use lurk::{fib::lurk_fib, lem::store::Store, state::State};

fn main() {
    let store = &Store::<Fq>::default();
    let n: usize = std::env::args().collect::<Vec<_>>()[1].parse().unwrap();
    let state = State::init_lurk_state();

    let fib = lurk_fib(store, n);

    println!("Fib({n}) = {}", fib.fmt_to_string(store, &state));
}
