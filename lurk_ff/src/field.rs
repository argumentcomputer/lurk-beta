use ff::{
  PrimeField,
  PrimeFieldBits,
};

use crate::tag::{
  ContTag,
  ExprTag,
  FieldKind,
  Op1,
  Op2,
  Tag,
  TagKind,
  Version,
};

const CURRENT_VERSION: Version = Version { major: 0, minor: 0, patch: 0 };

pub trait LurkField: PrimeField + PrimeFieldBits {
  const VERSION: Version;
  const FIELD_KIND: FieldKind;

  fn from_repr_bytes(bs: &[u8]) -> Option<Self> {
    let mut def: Self::Repr = Self::default().to_repr();
    def.as_mut().copy_from_slice(bs);
    Self::from_repr(def).into()
  }

  fn to_le_bytes(self) -> Vec<u8> {
    let mut vec = vec![];
    let bits = self.to_le_bits();

    let len = bits.len();
    let len_bytes = if len % 8 != 0 { len / 8 + 1 } else { len / 8 };
    for _ in 0..len_bytes {
      vec.push(0u8)
    }
    let mut n = 0;
    for b in bits {
      let (byte_i, bit_i) = (n / 8, n % 8);
      if b {
        vec[byte_i] = vec[byte_i] | (1u8 << bit_i);
      }
      n += 1;
    }
    vec
  }

  fn hex_digits(self) -> String {
    let mut s = String::new();
    let bytes = self.to_le_bytes();
    for b in bytes.iter().rev() {
      s.push_str(&format!("{:02x?}", b));
    }
    s
  }

  // TODO: detect overflow?
  fn from_le_bytes(bs: &[u8]) -> Self {
    let mut res = Self::zero();
    let mut bs = bs.iter().rev().peekable();
    while let Some(b) = bs.next() {
      let b: Self = (*b as u64).into();
      if let None = bs.peek() {
        res.add_assign(b)
      }
      else {
        res.add_assign(b);
        res.mul_assign(Self::from(256u64.into()));
      }
    }
    res
  }

  fn to_repr_bytes(self) -> Vec<u8> {
    let repr = self.to_repr();
    repr.as_ref().to_vec()
  }

  fn vec_f_to_bytes(vec_f: Vec<Self>) -> Vec<u8> {
    let mut vec = vec![];
    for f in vec_f {
      for byte in f.to_repr_bytes() {
        vec.push(byte)
      }
    }
    vec
  }
  fn vec_f_from_bytes(vec: &[u8]) -> Option<Vec<Self>> {
    let num_bytes: usize = (Self::NUM_BITS / 8 + 1) as usize;
    let mut vec_f: Vec<Self> = vec![];
    for chunk in vec.chunks(num_bytes) {
      let f: Self = Self::from_repr_bytes(&chunk)?;
      vec_f.push(f);
    }
    Some(vec_f)
  }

  fn to_u16(&self) -> Option<u16> {
    for x in &self.to_repr().as_ref()[2..] {
      if *x != 0 {
        return None;
      }
    }
    let mut byte_array = [0u8; 2];
    byte_array.copy_from_slice(&self.to_repr().as_ref()[0..2]);
    Some(u16::from_le_bytes(byte_array))
  }
  fn to_u32(&self) -> Option<u32> {
    for x in &self.to_repr().as_ref()[4..] {
      if *x != 0 {
        return None;
      }
    }
    let mut byte_array = [0u8; 4];
    byte_array.copy_from_slice(&self.to_repr().as_ref()[0..4]);
    Some(u32::from_le_bytes(byte_array))
  }
  fn to_char(&self) -> Option<char> {
    let x = self.to_u32()?;
    char::from_u32(x)
  }
  fn to_u64(&self) -> Option<u64> {
    for x in &self.to_repr().as_ref()[8..] {
      if *x != 0 {
        return None;
      }
    }
    let mut byte_array = [0u8; 8];
    byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
    Some(u64::from_le_bytes(byte_array))
  }
  // Return a u64 corresponding to the first 8 little-endian bytes of this field
  // element, discarding the remaining bytes.
  fn to_u64_unchecked(&self) -> u64 {
    let mut byte_array = [0u8; 8];
    byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
    u64::from_le_bytes(byte_array)
  }

  fn from_u64(x: u64) -> Self { x.into() }

  fn from_u32(x: u32) -> Self { (x as u64).into() }

  fn from_char(x: char) -> Self { Self::from_u32(x as u32) }

  fn most_negative() -> Self { Self::most_positive() + Self::one() }

  /// 0 - 1 is one minus the modulus, which must be even in a prime field.
  /// The result is the largest field element which is even when doubled.
  /// We define this to be the most positive field element.
  fn most_positive() -> Self {
    let one = Self::one();
    let two = one + one;

    let half = two.invert().unwrap();
    let modulus_minus_one = Self::zero() - one;
    half * modulus_minus_one
  }

  /// A field element is defined to be negative if it is odd after doubling.
  fn is_negative(&self) -> bool { self.double().is_odd().into() }

  /// This function does not check that the resulting version and field
  /// match the trait constants
  fn from_tag_unchecked(tag: Tag) -> Self { Self::from_u64(tag.into()) }

  fn from_tag(tag: Tag) -> Option<Self> {
    if tag.version == Self::VERSION && tag.field == Self::FIELD_KIND {
      Some(Self::from_u64(tag.into()))
    }
    else {
      None
    }
  }

  fn make_tag(kind: TagKind) -> Tag {
    Tag { version: Self::VERSION, field: Self::FIELD_KIND, kind }
  }

  fn make_expr_tag(expr_tag: ExprTag) -> Tag {
    Tag {
      version: Self::VERSION,
      field: Self::FIELD_KIND,
      kind: TagKind::Expr(expr_tag),
    }
  }

  fn make_cont_tag(cont_tag: ContTag) -> Tag {
    Tag {
      version: Self::VERSION,
      field: Self::FIELD_KIND,
      kind: TagKind::Cont(cont_tag),
    }
  }

  fn make_op1_tag(op1_tag: Op1) -> Tag {
    Tag {
      version: Self::VERSION,
      field: Self::FIELD_KIND,
      kind: TagKind::Op1(op1_tag),
    }
  }

  fn make_op2_tag(kind: Op2) -> Tag {
    Tag {
      version: Self::VERSION,
      field: Self::FIELD_KIND,
      kind: TagKind::Op2(kind),
    }
  }

  fn to_tag(&self) -> Option<Tag> {
    let x = Self::to_u64(self)?;
    Tag::try_from(x).ok()
  }

  fn get_version(&self) -> Option<Version> { Some(Self::to_tag(self)?.version) }

  fn get_tag_kind(&self) -> Option<TagKind> { Some(Self::to_tag(self)?.kind) }

  fn get_field_kind(&self) -> Option<FieldKind> {
    Some(Self::to_tag(self)?.field)
  }
}

impl LurkField for blstrs::Scalar {
  const FIELD_KIND: FieldKind = FieldKind::BLS12_381;
  const VERSION: Version = CURRENT_VERSION;
}

impl LurkField for pasta_curves::Fp {
  const FIELD_KIND: FieldKind = FieldKind::Pallas;
  const VERSION: Version = CURRENT_VERSION;
}

impl LurkField for pasta_curves::Fq {
  const FIELD_KIND: FieldKind = FieldKind::Vesta;
  const VERSION: Version = CURRENT_VERSION;
}

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  // For working around the orphan trait impl rule
  #[derive(Clone, Debug, PartialEq, Eq)]
  pub struct FWrap<F: LurkField>(pub F);

  impl<F: LurkField> Arbitrary for FWrap<F> {
    fn arbitrary(_: &mut Gen) -> Self {
      let f = F::random(rand::thread_rng());
      FWrap(f)
    }
  }

  // For working around the orphan trait impl rule
  #[derive(Clone, Debug, PartialEq, Eq)]
  pub struct VecFWrap<F: LurkField>(pub Vec<F>);

  impl<F: LurkField> Arbitrary for VecFWrap<F> {
    fn arbitrary(g: &mut Gen) -> Self {
      let vec_f: Vec<FWrap<F>> = Arbitrary::arbitrary(g);
      VecFWrap(vec_f.into_iter().map(|f| f.0).collect())
    }
  }
}

#[cfg(test)]
pub mod tests {
  use blstrs::Scalar as Fr;
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::{
    test_utils::*,
    *,
  };

  #[quickcheck]
  fn prop_repr_bytes_consistency(f1: FWrap<Fr>) -> bool {
    let bytes = f1.0.to_repr().as_ref().to_owned();
    let f2 = <Fr as LurkField>::from_repr_bytes(&bytes);
    Some(f1.0) == f2
  }

  #[quickcheck]
  fn prop_byte_digits_consistency(f1: FWrap<Fr>) -> bool {
    let bytes = f1.0.to_le_bytes();
    let f2 = Fr::from_le_bytes(&bytes);
    println!("{:?}", bytes);
    println!("f1 0x{}", f1.0.hex_digits());
    println!("f2 0x{}", f2.hex_digits());
    Some(f1.0) == Some(f2)
  }

  #[quickcheck]
  fn prop_tag_consistency(x: Tag) -> bool {
    let f1 = Fr::from_tag_unchecked(x);
    let tag = <Fr as LurkField>::to_tag(&f1).unwrap();
    let f2 = Fr::from_tag_unchecked(tag);
    f1 == f2 && x == tag
  }

  #[quickcheck]
  fn prop_vec_f_consistency(vec_f: VecFWrap<Fr>) -> bool {
    let bytes = Fr::vec_f_to_bytes(vec_f.0.clone());
    match Fr::vec_f_from_bytes(&bytes) {
      Some(vec_f2) => vec_f.0 == vec_f2,
      None => false,
    }
  }
}
