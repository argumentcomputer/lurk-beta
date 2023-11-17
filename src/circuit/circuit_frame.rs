use bellpepper::util_cs::Comparable;

use crate::field::LurkField;

/// Prints out the full CS for debugging purposes
#[allow(dead_code)]
pub(crate) fn print_cs<F: LurkField, C: Comparable<F>>(this: &C) -> String {
    let mut out = String::new();
    out += &format!("num_inputs: {}\n", this.num_inputs());
    out += &format!("num_constraints: {}\n", this.num_constraints());
    out += "\ninputs:\n";
    for (i, input) in this.inputs().iter().enumerate() {
        out += &format!("{i}: {input}\n");
    }
    out += "\nconstraints:\n";
    for (i, cs) in this.constraints().iter().enumerate() {
        out += &format!(
            "{}: {}:\n  {:?}\n  {:?}\n  {:?}\n",
            i,
            cs.3,
            cs.0.iter().collect::<Vec<_>>(),
            cs.1.iter().collect::<Vec<_>>(),
            cs.2.iter().collect::<Vec<_>>()
        );
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::gadgets::constraints::implies_pack;
    use crate::circuit::gadgets::constraints::popcount_equal;
    use bellpepper_core::boolean::Boolean;
    use bellpepper_core::num::AllocatedNum;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bellpepper_core::ConstraintSystem;

    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn test_enforce_popcount() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        for x in 0..128 {
            let alloc_a =
                AllocatedNum::alloc(&mut cs.namespace(|| x.to_string()), || Ok(Fr::from(x)))
                    .unwrap();
            let bits = alloc_a
                .to_bits_le(&mut cs.namespace(|| format!("bits_{x}")))
                .unwrap();
            let popcount_result =
                AllocatedNum::alloc(&mut cs.namespace(|| format!("alloc popcount {x}")), || {
                    Ok(Fr::from(u64::from(x.count_ones())))
                })
                .unwrap();

            popcount_equal(
                &mut cs.namespace(|| format!("popcount {x}")),
                &bits,
                popcount_result.get_variable(),
            );
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_pack() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let a_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "a num"), || Fr::from_u64(42));
        let bits = a_num.to_bits_le(&mut cs.namespace(|| "bits")).unwrap();
        implies_pack(&mut cs, &Boolean::Constant(true), &bits, &a_num);
        assert!(cs.is_satisfied());
    }
}
