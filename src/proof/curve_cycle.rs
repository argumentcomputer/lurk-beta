#![allow(non_snake_case)]

use nova::{
    provider::bn256_grumpkin::{bn256, grumpkin},
    provider::pedersen::CommitmentKeyExtTrait,
    traits::{circuit::TrivialTestCircuit, commitment::CommitmentEngineTrait, Group},
};
use pasta_curves::{pallas, vesta};

use crate::field::LurkField;

/// This trait defines most of the requirements for programming generically over the supported Nova curve cycles
/// (currently Pallas/Vesta and BN254/Grumpkin). It being pegged on the `LurkField` trait encodes that we do
/// not expect more than one such cycle to be supported at a time for a given field.
pub trait CurveCycleEquipped: LurkField {
    /// ## Why the next 4 types?
    ///
    /// The next 4 types are purely technical, and aim at laying out type bounds in a way that rust can find them.
    /// They should eventually be replaceable by a bound on projections, once bounds on associated types progress.
    /// They are technically equivalent to bounds of
    ///  <Self::G1::CE as CommitmentEngineTrait<Self::G1>>::CommitmentKey: CommitmentKeyExtTrait<Self::G1, CE = <Self::G1 as Group>::CE>,
    ///  <Self::G2::CE as CommitmentEngineTrait<Self::G2>>::CommitmentKey: CommitmentKeyExtTrait<Self::G2, CE = <G2 as Group>::CE>,
    /// but where clauses can't be *found* by the compiler at the point where Self::G1, Self::G2 are used

    /// ## OK, but why do we need bounds at all in the first place?
    ///
    /// As to *why* those see https://github.com/microsoft/Nova/pull/200
    /// and the bound `CommitmentKey<G>: CommitmentKeyExtTrait<G, CE = G::CE>` on [`nova::provider::ipa_pc::EvaluationEngine<G>`]
    /// Essentially, Nova relies on a commitment scheme that is additively homomorphic, but encodes the practicalities of this
    /// (properties are unwieldy to encode) in the form of this CommitmentKeyExtTrait.

    /// The type of the commitment key used for points of the first curve in the cycle.
    type CK1: CommitmentKeyExtTrait<Self::G1>;
    /// The type of the commitment key used for points of the second curve in the cycle.
    type CK2: CommitmentKeyExtTrait<Self::G2>;
    /// The commitment engine type for the first curve in the cycle.
    type CE1: CommitmentEngineTrait<Self::G1, CommitmentKey = Self::CK1>;
    /// The commitment engine type for the second curve in the cycle.
    type CE2: CommitmentEngineTrait<Self::G2, CommitmentKey = Self::CK2>;

    /// The group type for the first curve in the cycle.
    type G1: Group<Base = <Self::G2 as Group>::Scalar, Scalar = Self, CE = Self::CE1>;
    /// The  group type for the second curve in the cycle.
    type G2: Group<Base = <Self::G1 as Group>::Scalar, CE = Self::CE2>;
}

impl CurveCycleEquipped for pallas::Scalar {
    type CK1 = nova::provider::pedersen::CommitmentKey<pallas::Point>;
    type CK2 = nova::provider::pedersen::CommitmentKey<vesta::Point>;
    type CE1 = nova::provider::pedersen::CommitmentEngine<pallas::Point>;
    type CE2 = nova::provider::pedersen::CommitmentEngine<vesta::Point>;

    type G1 = pallas::Point;
    type G2 = vesta::Point;
}
// The impl CurveCycleEquipped for vesta::Scalar is academically possible, but voluntarily omitted to avoid confusion.

impl CurveCycleEquipped for bn256::Scalar {
    type CK1 = nova::provider::pedersen::CommitmentKey<bn256::Point>;
    type CK2 = nova::provider::pedersen::CommitmentKey<grumpkin::Point>;
    type CE1 = nova::provider::pedersen::CommitmentEngine<bn256::Point>;
    type CE2 = nova::provider::pedersen::CommitmentEngine<grumpkin::Point>;

    type G1 = bn256::Point;
    type G2 = grumpkin::Point;
}
// The impl CurveCycleEquipped for grumpkin::Scalar is academically possible, but voluntarily omitted to avoid confusion.

/// Convenience alias for the primary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type G1<F> = <F as CurveCycleEquipped>::G1;
/// Convenience alias for the secondary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type G2<F> = <F as CurveCycleEquipped>::G2;

/// Type alias for the Evaluation Engine using G1 group elements.
pub type EE1<F> = nova::provider::ipa_pc::EvaluationEngine<G1<F>>;
/// Type alias for the Evaluation Engine using G2 group elements.
pub type EE2<F> = nova::provider::ipa_pc::EvaluationEngine<G2<F>>;

/// Type alias for the Relaxed R1CS Spartan SNARK using G1 group elements, EE1.
/// NOTE: this is not a SNARK that uses computational commitments,
/// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS1<F> = nova::spartan::snark::RelaxedR1CSSNARK<G1<F>, EE1<F>>;
/// Type alias for the Relaxed R1CS Spartan SNARK using G2 group elements, EE2.
/// NOTE: this is not a SNARK that uses computational commitments,
/// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS2<F> = nova::spartan::snark::RelaxedR1CSSNARK<G2<F>, EE2<F>>;

/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialTestCircuit<<G2<F> as Group>::Scalar>;
