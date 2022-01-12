use super::constraints::{add, alloc_is_zero, equal, mul, pick, select, sub};
use bellperson::{
    gadgets::boolean::{AllocatedBit, Boolean},
    gadgets::num::AllocatedNum,
    ConstraintSystem, LinearCombination, SynthesisError,
};
use blstrs::Scalar as Fr;
use ff::{Field, PrimeField};

use std::ops::{MulAssign, SubAssign};

pub struct CaseClause<F: PrimeField> {
    pub key: F,
    pub value: AllocatedNum<F>,
}

pub struct CaseConstraint<'a, F: PrimeField> {
    selected: AllocatedNum<F>,
    clauses: &'a [CaseClause<F>],
}

impl CaseConstraint<'_, Fr> {
    fn enforce_selection<CS: ConstraintSystem<Fr>>(
        self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
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
                    .zip(&*self.clauses)
                    .fold(lc, |lc, (selector, clause)| {
                        lc + (clause.key, selector.get_variable())
                    })
            },
            |lc| lc + CS::one(),
            |lc| lc + self.selected.get_variable(),
        );

        let values = self
            .clauses
            .iter()
            .map(|c| c.value.clone())
            .collect::<Vec<_>>();

        let result = bit_dot_product(
            &mut cs.namespace(|| "extract result"),
            &selectors,
            values.as_slice(),
        )?;

        Ok(result)
    }
}

fn bit_dot_product<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    bit_vector: &[AllocatedBit],
    value_vector: &[AllocatedNum<Fr>],
) -> Result<AllocatedNum<Fr>, SynthesisError> {
    let mut computed_result = Fr::zero();

    let mut all_products = Vec::new();
    let zero = AllocatedNum::alloc(&mut cs.namespace(|| "zero"), || Ok(Fr::zero()))?;

    for (i, (bit, value)) in bit_vector.iter().zip(value_vector).enumerate() {
        let allocated_prod = pick(
            &mut cs.namespace(|| format!("allocated_prod {}", i)),
            &Boolean::Is(bit.clone()),
            value,
            &zero,
        )?;

        all_products.push(allocated_prod.clone());

        if let Some(prod) = allocated_prod.get_value() {
            computed_result += prod;
        };
    }
    let result = AllocatedNum::<Fr>::alloc(&mut cs.namespace(|| "result"), || Ok(computed_result))?;

    cs.enforce(
        || "sum of products",
        |lc| {
            all_products
                .iter()
                .fold(lc, |acc, prod| acc + prod.get_variable())
        },
        |lc| lc + CS::one(),
        |lc| lc + result.get_variable(),
    );

    Ok(result)
}

pub fn case<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    selected: &AllocatedNum<Fr>,
    clauses: &[CaseClause<Fr>],
    default: &AllocatedNum<Fr>,
) -> Result<AllocatedNum<Fr>, SynthesisError> {
    assert!(!clauses.is_empty());

    let mut any_selected = false;

    let mut acc = AllocatedNum::alloc(cs.namespace(|| "acc"), || Ok(Fr::one()))?;

    for (i, clause) in clauses.iter().enumerate() {
        if Some(clause.key) == selected.get_value() {
            any_selected = true;
        }

        let mut x = clause.key;
        let mut selected_present = false;

        if let Some(s) = selected.get_value() {
            selected_present = true;
            x.sub_assign(&s);
        };

        if let Some(a) = acc.get_value() {
            x.mul_assign(&a)
        };

        let new_acc = AllocatedNum::alloc(&mut cs.namespace(|| format!("acc {}", i + 1)), || {
            if selected_present {
                Ok(x)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        // acc * clause.key - selected = new_acc
        cs.enforce(
            || format!("acc * (clause-{}.key - selected) = new_acc", i),
            |lc| lc + acc.get_variable(),
            |_| Boolean::Constant(true).lc(CS::one(), clause.key) - selected.get_variable(),
            |lc| lc + new_acc.get_variable(),
        );

        acc = new_acc;
    }
    let is_selected = alloc_is_zero(cs.namespace(|| "is_selected"), &acc)?;
    // If no selection matched, use a dummy key so constraints are met.
    // We will actually return the default value, though.
    let dummy_key = clauses[0].key;
    let selected = AllocatedNum::alloc(cs.namespace(|| "default key"), || {
        if any_selected {
            selected
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)
        } else {
            Ok(dummy_key)
        }
    })?;

    // FIXME: Ensure cases contain no duplicate keys.
    let cc = CaseConstraint { selected, clauses };

    // If no selection matched, choose the default value.
    let is_default = is_selected.not();

    let enforced_result = cc.enforce_selection(cs)?;

    pick(
        &mut cs.namespace(|| "maybe default"),
        &is_default,
        default,
        &enforced_result,
    )
}

// TODO: This can be optimized to minimize work duplicated between the inner case calls.
pub fn multi_case<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    selected: &AllocatedNum<Fr>,
    cases: &[&[CaseClause<Fr>]],
    defaults: &[AllocatedNum<Fr>],
) -> Result<Vec<AllocatedNum<Fr>>, SynthesisError> {
    let mut result = Vec::new();

    for (i, (c, default)) in cases.iter().zip(defaults).enumerate() {
        result.push(case(
            &mut cs.namespace(|| format!("case {}", i)),
            selected,
            c,
            default,
        )?);
    }
    Ok(result)
}
mod tests {
    use super::*;
    use bellperson::util_cs::{
        metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta,
    };
    use ff::PrimeField;

    use crate::data::fr_from_u64;

    #[test]
    fn simple_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let x = fr_from_u64(123);
        let y = fr_from_u64(124);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let val = AllocatedNum::alloc(cs.namespace(|| "val"), || Ok(fr_from_u64(666))).unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(fr_from_u64(777))).unwrap();
        let default =
            AllocatedNum::alloc(cs.namespace(|| "default"), || Ok(fr_from_u64(999))).unwrap();

        {
            let clauses = [
                CaseClause {
                    key: x,
                    value: val.clone(),
                },
                CaseClause {
                    key: y,
                    value: val2.clone(),
                },
            ];

            let result = case(
                &mut cs.namespace(|| "selected case"),
                &selected,
                &clauses,
                &default,
            )
            .unwrap();

            assert_eq!(val.get_value(), result.get_value());
            assert!(cs.is_satisfied());
        }

        {
            let clauses = [CaseClause {
                key: y,
                value: val.clone(),
            }];

            let result = case(
                &mut cs.namespace(|| "default case"),
                &selected,
                &clauses,
                &default,
            )
            .unwrap();

            assert_eq!(default.get_value(), result.get_value());
            assert!(cs.is_satisfied());
        }
    }
    #[test]
    fn groth_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut cs_blank = MetricCS::<Fr>::new();

        let x = fr_from_u64(123);
        let y = fr_from_u64(124);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let selected_blank = AllocatedNum::alloc(cs_blank.namespace(|| "selected"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();
        let val = AllocatedNum::alloc(cs.namespace(|| "val"), || Ok(fr_from_u64(666))).unwrap();
        let val_blank = AllocatedNum::alloc(cs_blank.namespace(|| "val"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(fr_from_u64(777))).unwrap();
        let val2_blank = AllocatedNum::alloc(cs_blank.namespace(|| "val2"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();
        let default =
            AllocatedNum::alloc(cs.namespace(|| "default"), || Ok(fr_from_u64(999))).unwrap();
        let default_blank =
            AllocatedNum::alloc(cs_blank.namespace(|| "default"), || Ok(fr_from_u64(999))).unwrap();

        {
            let clauses = [
                CaseClause {
                    key: x,
                    value: val.clone(),
                },
                CaseClause {
                    key: y,
                    value: val2.clone(),
                },
            ];

            let result = case(
                &mut cs.namespace(|| "selected case"),
                &selected,
                &clauses,
                &default,
            )
            .unwrap();

            assert_eq!(val.get_value(), result.get_value());
            assert!(cs.is_satisfied());
        }
        {
            let clauses_blank = [
                CaseClause {
                    key: x,
                    value: val_blank.clone(),
                },
                CaseClause {
                    key: y,
                    value: val2_blank.clone(),
                },
            ];

            let result = case(
                &mut cs_blank.namespace(|| "selected case"),
                &selected,
                &clauses_blank,
                &default_blank,
            )
            .unwrap();

            assert!(cs.is_satisfied());
        }

        let delta = cs.delta(&cs_blank, false);
        assert!(delta == Delta::Equal);
    }
}
