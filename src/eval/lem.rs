use crate::field::LurkField;

/// Lurk Evaluation Model
pub struct LEM<'a, F: LurkField> {
    input: Vec<&'a str>,
    output: Vec<&'a str>,
    ops: Vec<OP<'a, F>>,
}

pub enum OP<'a, F: LurkField> {
    /// `Set(dst, x)` sets `dst` with value `x`
    Set(&'a str, F),
    /// `Copy(dst, src)` copies `src` to `dst`
    Copy(&'a str, &'a str),
    /// `Hash2(dst, i)` sets `dst` as the arity-2 hash of `i`
    Hash2(&'a str, [&'a str; 2]),
    /// `Hash3(dst, i)` sets `dst` as the arity-3 hash of `i`
    Hash3(&'a str, [&'a str; 3]),
    /// `Hash4(dst, i)` sets `dst` as the arity-4 hash of `i`
    Hash4(&'a str, [&'a str; 4]),
    /// `Hash6(dst, i)` sets `dst` as the arity-6 hash of `i`
    Hash6(&'a str, [&'a str; 6]),
    /// `Car(dst, cdr_wit, cons)` sets `dst` with the car of `cons`
    Car([&'a str; 2], [&'a str; 2], [&'a str; 2]),
    /// `Cdr(dst, cdr_wit, cons)` sets `dst` with the cdr of `cons`
    Cdr([&'a str; 2], [&'a str; 2], [&'a str; 2]),
    /// `Fork(prop, tt, ff)` runs `tt` if `prop` is not zero and `ff` otherwise
    Fork(&'a str, Vec<Box<OP<'a, F>>>, Vec<Box<OP<'a, F>>>),
    /// `Match(var, [(val1, ops1), (val2, ops2), ...], def)` does a match on the
    /// value of `var`, running `ops1` if it equals to `val1, or `ops2` if it
    /// equals `val2, so on and so forth. If no match is found, run `def` as the
    /// default option
    Match(&'a str, Vec<(F, Box<OP<'a, F>>)>, Box<OP<'a, F>>),
}

pub enum ExprTag {
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Name,
    Sym,
    Key,
}

impl ExprTag {
    pub fn to_field<F: LurkField>(self) -> F {
        todo!()
    }
}

pub enum ContTag {}

impl ContTag {
    pub fn to_field<F: LurkField>(self) -> F {
        todo!()
    }
}

impl<'a, F: LurkField> LEM<'a, F> {
    pub fn mk_fun(o: [&'a str; 2], i: [&'a str; 6]) -> Vec<OP<'a, F>> {
        vec![OP::Set(o[0], ExprTag::Fun.to_field()), OP::Hash6(o[1], i)]
    }

    pub fn mk_comm(o: [&'a str; 2], i: [&'a str; 3]) -> Vec<OP<'a, F>> {
        vec![OP::Set(o[0], ExprTag::Comm.to_field()), OP::Hash3(o[1], i)]
    }

    pub fn mk_cons(o: [&'a str; 2], i: [&'a str; 4]) -> Vec<OP<'a, F>> {
        vec![OP::Set(o[0], ExprTag::Cons.to_field()), OP::Hash4(o[1], i)]
    }

    pub fn mk_strcons(o: [&'a str; 2], i: [&'a str; 4]) -> Vec<OP<'a, F>> {
        vec![OP::Set(o[0], ExprTag::Str.to_field()), OP::Hash4(o[1], i)]
    }

    pub fn check(&self) {
        assert!(
            self.input.len() == self.output.len(),
            "Input and output must have the same length"
        );
        for s in self.input.iter() {
            assert!(
                !self.output.contains(&s),
                "Input and output must be disjoint"
            )
        }
        let mut available_slots = self.input.clone();
        for op in self.ops.iter() {
            // TODO: assert that used slots have been previously defined
            // TODO: assert that input slots aren't overwritten
            // TODO: assert that no slot is overwritten within a fork or match arm
            // TODO: assert that all input slots are used
            // TODO: assert that all output slots are set
        }
    }

    pub fn count_constraints(&self) -> usize {
        todo!()
    }
}
