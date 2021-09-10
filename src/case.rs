use bellperson::{
    bls::Engine, gadgets::boolean::AllocatedBit, gadgets::num::AllocatedNum, ConstraintSystem,
    SynthesisError,
};
use ff::Field;

struct CaseClause<E: Engine> {
    key: E::Fr,
    value: AllocatedNum<E>,
}

struct CaseConstraint<E: Engine> {
    selected: AllocatedNum<E>,
    clauses: Vec<CaseClause<E>>,
}

impl<E: Engine> CaseConstraint<E> {
    fn select<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        let mut result = AllocatedNum::alloc(cs.namespace(|| "result"), || Ok(E::Fr::zero()))?;

        // Allocate one bit per clause, the selector. This creates constraints enforcing that each bit is 0 or 1.
        // In fact, the 'selected' clause will have selector = 1 while the others = 0.
        // This will be confirmed/enforced by later constraints.
        let mut selectors = Vec::with_capacity(self.clauses.len());
        for (i, clause) in self.clauses.iter().enumerate() {
            let is_selected = if let Some(value) = self.selected.get_value() {
                clause.key == value
            } else {
                false
            };
            selectors.push(
                AllocatedBit::alloc(
                    cs.namespace(|| format!("selector {}", i)),
                    Some(is_selected),
                )
                .unwrap(),
            );
            if is_selected {
                result = clause.value.clone();
            }
        }

        cs.enforce(
            || "exactly one selector is 1",
            |lc| {
                selectors
                    .iter()
                    .fold(lc, |lc, selector| lc + selector.get_variable())
            },
            |lc| lc + CS::one(),
            |lc| lc + CS::one(),
        );

        cs.enforce(
            || "selection vector dot keys = selected",
            |lc| {
                selectors
                    .iter()
                    .zip(&self.clauses)
                    .fold(lc, |lc, (selector, clause)| {
                        lc + (clause.key, selector.get_variable())
                    })
            },
            |lc| lc + CS::one(),
            |lc| lc + self.selected.get_variable(),
        );

        cs.enforce(
            || "selection vector dot values = result",
            |lc| {
                selectors
                    .iter()
                    .fold(lc, |lc, selector| lc + selector.get_variable())
            },
            |lc| {
                self.clauses
                    .iter()
                    .fold(lc, |lc, clause| lc + clause.value.get_variable())
            },
            |lc| lc + result.get_variable(),
        );

        Ok(result)
    }
}

// fn case<E: Engine, CS: ConstraintSystem<E>>(cs: mut CS) -> Result<AllocatedNum<E>, SynthesisError> {

// }
