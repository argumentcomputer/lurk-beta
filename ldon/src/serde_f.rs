use lurk_ff::field::LurkField;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SerdeFError<F: LurkField> {
  UnexpectedEnd,
  ExpectedU64(F),
  ByteRead(Vec<u8>),
  UnknownTag(F),
  Expected(String),
  Custom(String),
}

pub trait SerdeF<F: LurkField> {
  fn ser_f(&self) -> Vec<F>;
  fn de_f(fs: &[F]) -> Result<Self, SerdeFError<F>>
  where Self: Sized;

  fn ser(&self) -> Vec<u8> { F::vec_f_to_bytes(self.ser_f()) }

  fn de(fs: &[u8]) -> Result<Self, SerdeFError<F>>
  where Self: Sized {
    let vec_f = F::vec_f_from_bytes(fs)
      .ok_or_else(|| SerdeFError::ByteRead(Vec::from(fs)))?;
    Self::de_f(&vec_f)
  }
}
