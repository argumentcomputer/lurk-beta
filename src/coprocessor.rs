use std::fmt::Debug;

use crate::eval::IO;
use crate::field::LurkField;

use crate::store::{ContPtr, Ptr, Store};

pub trait Coprocessor<F: LurkField>: Debug + Sync {
    fn arity(&self) -> usize;

    fn evaluate(&self, s: &mut Store<F>, args: Ptr<F>, env: Ptr<F>, cont: ContPtr<F>) -> IO<F> {
        let argv: Vec<Ptr<F>> = s.fetch_list(&args);

        use crate::writer::Write;
        dbg!(args.fmt_to_string(s));
        assert_eq!(argv.len(), self.arity());

        let result = self.simple_evaluate(s, &argv);

        IO {
            expr: result,
            env,
            cont,
        }
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F>;
}
