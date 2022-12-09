use std::{
  convert::TryFrom,
  fmt,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Tag {
  pub version: Version, // u32
  pub field: FieldKind, // u16
  pub kind: TagKind,    // u16
}

impl From<Tag> for u64 {
  fn from(val: Tag) -> Self {
    let v: u32 = val.version.into();
    let t: u16 = val.kind.into();
    ((v as u64) << 32) + ((val.field as u64) << 16) + (t as u64)
  }
}

impl TryFrom<u64> for Tag {
  type Error = String;

  fn try_from(f: u64) -> Result<Self, Self::Error> {
    let version = Version::from((f >> 32) as u32);
    let field = FieldKind::try_from(((f & 0xffff_0000) >> 16) as u16)?;
    let kind = TagKind::try_from((f & 0xffff) as u16)?;
    Ok(Tag { version, field, kind })
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum FieldKind {
  BLS12_381 = 0b0000_0000_0000_0000,
  Pallas,
  Vesta,
}

impl From<FieldKind> for u16 {
  fn from(val: FieldKind) -> Self { val as u16 }
}

impl TryFrom<u16> for FieldKind {
  type Error = String;

  fn try_from(x: u16) -> Result<Self, Self::Error> {
    match x {
      f if f == FieldKind::BLS12_381 as u16 => Ok(FieldKind::BLS12_381),
      f if f == FieldKind::Pallas as u16 => Ok(FieldKind::Pallas),
      f if f == FieldKind::Vesta as u16 => Ok(FieldKind::Vesta),
      x => Err(format!("Invalid FieldKind value: {}", x)),
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Version {
  pub major: u16,
  pub minor: u8,
  pub patch: u8,
}

impl From<Version> for u32 {
  fn from(val: Version) -> Self {
    ((val.major as u32) << 16) + ((val.minor as u32) << 8) + (val.patch as u32)
  }
}

impl From<u32> for Version {
  fn from(x: u32) -> Self {
    Version {
      major: (x >> 16) as u16,
      minor: ((x >> 8) & 0xff) as u8,
      patch: (x & 0xff) as u8,
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TagKind {
  Expr(ExprTag),
  Cont(ContTag),
  Op1(Op1),
  Op2(Op2),
}

impl fmt::Display for TagKind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Expr(x) => write!(f, "{}", x),
      Self::Cont(x) => write!(f, "{}", x),
      Self::Op1(x) => write!(f, "{}", x),
      Self::Op2(x) => write!(f, "{}", x),
    }
  }
}

impl From<TagKind> for u16 {
  fn from(val: TagKind) -> Self {
    match val {
      TagKind::Expr(x) => x as u16,
      TagKind::Cont(x) => x as u16,
      TagKind::Op1(x) => x as u16,
      TagKind::Op2(x) => x as u16,
    }
  }
}

impl TryFrom<u16> for TagKind {
  type Error = String;

  fn try_from(f: u16) -> Result<Self, Self::Error> {
    if let Ok(x) = ExprTag::try_from(f) {
      Ok(TagKind::Expr(x))
    }
    else if let Ok(x) = ContTag::try_from(f) {
      Ok(TagKind::Cont(x))
    }
    else if let Ok(x) = Op1::try_from(f) {
      Ok(TagKind::Op1(x))
    }
    else if let Ok(x) = Op2::try_from(f) {
      Ok(TagKind::Op2(x))
    }
    else {
      Err(format!("Invalid TagKind value: {}", f))
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum ExprTag {
  // Nil = Ptr { tag: Cons, val: F::zero()}
  Cons = 0b0000_0000_0000_0001,
  Sym,
  Fun,
  Num,
  Thunk,
  Str,
  Char,
  Comm,
  U64,
  Key,
  Map,
  Link,
}

impl From<ExprTag> for u16 {
  fn from(val: ExprTag) -> Self { val as u16 }
}

impl TryFrom<u16> for ExprTag {
  type Error = String;

  fn try_from(x: u16) -> Result<Self, Self::Error> {
    match x {
      f if f == ExprTag::Cons as u16 => Ok(ExprTag::Cons),
      f if f == ExprTag::Sym as u16 => Ok(ExprTag::Sym),
      f if f == ExprTag::Fun as u16 => Ok(ExprTag::Fun),
      f if f == ExprTag::Thunk as u16 => Ok(ExprTag::Thunk),
      f if f == ExprTag::Num as u16 => Ok(ExprTag::Num),
      f if f == ExprTag::Str as u16 => Ok(ExprTag::Str),
      f if f == ExprTag::Char as u16 => Ok(ExprTag::Char),
      f if f == ExprTag::Comm as u16 => Ok(ExprTag::Comm),
      f if f == ExprTag::U64 as u16 => Ok(ExprTag::U64),
      f if f == ExprTag::Key as u16 => Ok(ExprTag::Key),
      f if f == ExprTag::Map as u16 => Ok(ExprTag::Map),
      f if f == ExprTag::Link as u16 => Ok(ExprTag::Link),
      x => Err(format!("Invalid ExprTag value: {}", x)),
    }
  }
}

impl fmt::Display for ExprTag {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      ExprTag::Cons => write!(f, "cons#"),
      ExprTag::Sym => write!(f, "sym#"),
      ExprTag::Fun => write!(f, "fun#"),
      ExprTag::Num => write!(f, "num#"),
      ExprTag::Thunk => write!(f, "thunk#"),
      ExprTag::Str => write!(f, "str#"),
      ExprTag::Char => write!(f, "char#"),
      ExprTag::Comm => write!(f, "comm#"),
      ExprTag::U64 => write!(f, "u64#"),
      ExprTag::Key => write!(f, "key#"),
      ExprTag::Map => write!(f, "map#"),
      ExprTag::Link => write!(f, "link#"),
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum ContTag {
  Outermost = 0b0001_0000_0000_0000,
  Call0,
  Call,
  Call2,
  Tail,
  Error,
  Lookup,
  Unop,
  Binop,
  Binop2,
  If,
  Let,
  LetRec,
  Dummy,
  Terminal,
  Emit,
}

impl fmt::Display for ContTag {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      ContTag::Outermost => write!(f, "outermost#"),
      ContTag::Call0 => write!(f, "call0#"),
      ContTag::Call => write!(f, "call#"),
      ContTag::Call2 => write!(f, "call2#"),
      ContTag::Tail => write!(f, "tail#"),
      ContTag::Error => write!(f, "error#"),
      ContTag::Lookup => write!(f, "lookup#"),
      ContTag::Unop => write!(f, "unop#"),
      ContTag::Binop => write!(f, "binop#"),
      ContTag::Binop2 => write!(f, "binop2#"),
      ContTag::If => write!(f, "if#"),
      ContTag::Let => write!(f, "let#"),
      ContTag::LetRec => write!(f, "letrec#"),
      ContTag::Dummy => write!(f, "dummy#"),
      ContTag::Terminal => write!(f, "terminal#"),
      ContTag::Emit => write!(f, "emit#"),
    }
  }
}

impl From<ContTag> for u16 {
  fn from(val: ContTag) -> Self { val as u16 }
}

impl TryFrom<u16> for ContTag {
  type Error = String;

  fn try_from(x: u16) -> Result<Self, <ContTag as TryFrom<u16>>::Error> {
    match x {
      f if f == ContTag::Outermost as u16 => Ok(ContTag::Outermost),
      f if f == ContTag::Call0 as u16 => Ok(ContTag::Call0),
      f if f == ContTag::Call as u16 => Ok(ContTag::Call),
      f if f == ContTag::Call2 as u16 => Ok(ContTag::Call2),
      f if f == ContTag::Tail as u16 => Ok(ContTag::Tail),
      f if f == ContTag::Error as u16 => Ok(ContTag::Error),
      f if f == ContTag::Lookup as u16 => Ok(ContTag::Lookup),
      f if f == ContTag::Unop as u16 => Ok(ContTag::Unop),
      f if f == ContTag::Binop as u16 => Ok(ContTag::Binop),
      f if f == ContTag::Binop2 as u16 => Ok(ContTag::Binop2),
      f if f == ContTag::If as u16 => Ok(ContTag::If),
      f if f == ContTag::Let as u16 => Ok(ContTag::Let),
      f if f == ContTag::LetRec as u16 => Ok(ContTag::LetRec),
      f if f == ContTag::Dummy as u16 => Ok(ContTag::Dummy),
      f if f == ContTag::Terminal as u16 => Ok(ContTag::Terminal),
      f if f == ContTag::Emit as u16 => Ok(ContTag::Emit),
      x => Err(format!("Invalid ContTag value: {}", x)),
    }
  }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
#[repr(u16)]
pub enum Op1 {
  Car = 0b0010_0000_0000_0000,
  Cdr,
  Atom,
  Emit,
  Open,
  Secret,
  Commit,
  Num,
  Comm,
  Char,
  Eval,
  U64,
}

impl fmt::Display for Op1 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Op1::Car => write!(f, "car#"),
      Op1::Cdr => write!(f, "cdr#"),
      Op1::Atom => write!(f, "atom#"),
      Op1::Emit => write!(f, "emit#"),
      Op1::Open => write!(f, "open#"),
      Op1::Secret => write!(f, "secret#"),
      Op1::Commit => write!(f, "commit#"),
      Op1::Num => write!(f, "num#"),
      Op1::Comm => write!(f, "comm#"),
      Op1::Char => write!(f, "char#"),
      Op1::Eval => write!(f, "eval#"),
      Op1::U64 => write!(f, "u64#"),
    }
  }
}

impl From<Op1> for u16 {
  fn from(val: Op1) -> Self { val as u16 }
}

impl TryFrom<u16> for Op1 {
  type Error = String;

  fn try_from(x: u16) -> Result<Self, Self::Error> {
    match x {
      x if x == Op1::Car as u16 => Ok(Op1::Car),
      x if x == Op1::Cdr as u16 => Ok(Op1::Cdr),
      x if x == Op1::Atom as u16 => Ok(Op1::Atom),
      x if x == Op1::Emit as u16 => Ok(Op1::Emit),
      x if x == Op1::Open as u16 => Ok(Op1::Open),
      x if x == Op1::Secret as u16 => Ok(Op1::Secret),
      x if x == Op1::Commit as u16 => Ok(Op1::Commit),
      x if x == Op1::Num as u16 => Ok(Op1::Num),
      x if x == Op1::Comm as u16 => Ok(Op1::Comm),
      x if x == Op1::Char as u16 => Ok(Op1::Char),
      x if x == Op1::Eval as u16 => Ok(Op1::Eval),
      x if x == Op1::U64 as u16 => Ok(Op1::U64),
      x => Err(format!("Invalid Op1 value: {}", x)),
    }
  }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
#[repr(u16)]
pub enum Op2 {
  Sum = 0b0011_0000_0000_0000,
  Diff,
  Product,
  Quotient,
  Equal,
  NumEqual,
  Less,
  Greater,
  LessEqual,
  GreaterEqual,
  Cons,
  StrCons,
  Begin,
  Hide,
  Modulo,
  Eval,
}
impl fmt::Display for Op2 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Op2::Sum => write!(f, "sum#"),
      Op2::Diff => write!(f, "diff#"),
      Op2::Product => write!(f, "prod#"),
      Op2::Quotient => write!(f, "quot#"),
      Op2::Equal => write!(f, "eql#"),
      Op2::NumEqual => write!(f, "numeql#"),
      Op2::Less => write!(f, "lth#"),
      Op2::Greater => write!(f, "gth#"),
      Op2::LessEqual => write!(f, "leq#"),
      Op2::GreaterEqual => write!(f, "geq#"),
      Op2::Cons => write!(f, "cons#"),
      Op2::StrCons => write!(f, "strcons#"),
      Op2::Begin => write!(f, "begin#"),
      Op2::Hide => write!(f, "hide#"),
      Op2::Modulo => write!(f, "modulo#"),
      Op2::Eval => write!(f, "eval#"),
    }
  }
}

impl From<Op2> for u16 {
  fn from(val: Op2) -> Self { val as u16 }
}

impl TryFrom<u16> for Op2 {
  type Error = String;

  fn try_from(x: u16) -> Result<Self, Self::Error> {
    match x {
      x if x == Op2::Sum as u16 => Ok(Op2::Sum),
      x if x == Op2::Diff as u16 => Ok(Op2::Diff),
      x if x == Op2::Product as u16 => Ok(Op2::Product),
      x if x == Op2::Quotient as u16 => Ok(Op2::Quotient),
      x if x == Op2::Equal as u16 => Ok(Op2::Equal),
      x if x == Op2::NumEqual as u16 => Ok(Op2::NumEqual),
      x if x == Op2::Less as u16 => Ok(Op2::Less),
      x if x == Op2::Greater as u16 => Ok(Op2::Greater),
      x if x == Op2::LessEqual as u16 => Ok(Op2::LessEqual),
      x if x == Op2::GreaterEqual as u16 => Ok(Op2::GreaterEqual),
      x if x == Op2::Cons as u16 => Ok(Op2::Cons),
      x if x == Op2::StrCons as u16 => Ok(Op2::StrCons),
      x if x == Op2::Begin as u16 => Ok(Op2::Begin),
      x if x == Op2::Hide as u16 => Ok(Op2::Hide),
      x if x == Op2::Modulo as u16 => Ok(Op2::Modulo),
      x if x == Op2::Eval as u16 => Ok(Op2::Eval),
      x => Err(format!("Invalid Op2 value: {}", x)),
    }
  }
}

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;
  use crate::test_utils::frequency;
  impl Arbitrary for Version {
    fn arbitrary(g: &mut Gen) -> Self {
      Version {
        major: Arbitrary::arbitrary(g),
        minor: Arbitrary::arbitrary(g),
        patch: Arbitrary::arbitrary(g),
      }
    }
  }

  impl Arbitrary for FieldKind {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Self>)> = vec![
        (100, Box::new(|_| Self::BLS12_381)),
        (100, Box::new(|_| Self::Pallas)),
        (100, Box::new(|_| Self::Vesta)),
      ];
      frequency(g, input)
    }
  }

  impl Arbitrary for ExprTag {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Self>)> = vec![
        (100, Box::new(|_| Self::Cons)),
        (100, Box::new(|_| Self::Sym)),
        (100, Box::new(|_| Self::Fun)),
        (100, Box::new(|_| Self::Num)),
        (100, Box::new(|_| Self::Thunk)),
        (100, Box::new(|_| Self::Str)),
        (100, Box::new(|_| Self::Char)),
        (100, Box::new(|_| Self::Comm)),
        (100, Box::new(|_| Self::U64)),
      ];
      frequency(g, input)
    }
  }

  impl Arbitrary for ContTag {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Self>)> = vec![
        (100, Box::new(|_| Self::Outermost)),
        (100, Box::new(|_| Self::Call0)),
        (100, Box::new(|_| Self::Call)),
        (100, Box::new(|_| Self::Call2)),
        (100, Box::new(|_| Self::Tail)),
        (100, Box::new(|_| Self::Error)),
        (100, Box::new(|_| Self::Lookup)),
        (100, Box::new(|_| Self::Unop)),
        (100, Box::new(|_| Self::Binop)),
        (100, Box::new(|_| Self::Binop2)),
        (100, Box::new(|_| Self::If)),
        (100, Box::new(|_| Self::Let)),
        (100, Box::new(|_| Self::LetRec)),
        (100, Box::new(|_| Self::Dummy)),
        (100, Box::new(|_| Self::Terminal)),
        (100, Box::new(|_| Self::Emit)),
      ];
      frequency(g, input)
    }
  }
  impl Arbitrary for Op1 {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Self>)> = vec![
        (100, Box::new(|_| Self::Car)),
        (100, Box::new(|_| Self::Cdr)),
        (100, Box::new(|_| Self::Atom)),
        (100, Box::new(|_| Self::Emit)),
        (100, Box::new(|_| Self::Open)),
        (100, Box::new(|_| Self::Secret)),
        (100, Box::new(|_| Self::Commit)),
        (100, Box::new(|_| Self::Num)),
        (100, Box::new(|_| Self::Comm)),
        (100, Box::new(|_| Self::Char)),
        (100, Box::new(|_| Self::Eval)),
        (100, Box::new(|_| Self::U64)),
      ];
      frequency(g, input)
    }
  }
  impl Arbitrary for Op2 {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Self>)> = vec![
        (100, Box::new(|_| Self::Sum)),
        (100, Box::new(|_| Self::Diff)),
        (100, Box::new(|_| Self::Product)),
        (100, Box::new(|_| Self::Quotient)),
        (100, Box::new(|_| Self::Equal)),
        (100, Box::new(|_| Self::NumEqual)),
        (100, Box::new(|_| Self::Less)),
        (100, Box::new(|_| Self::Greater)),
        (100, Box::new(|_| Self::LessEqual)),
        (100, Box::new(|_| Self::GreaterEqual)),
        (100, Box::new(|_| Self::Cons)),
        (100, Box::new(|_| Self::StrCons)),
        (100, Box::new(|_| Self::Begin)),
        (100, Box::new(|_| Self::Hide)),
        (100, Box::new(|_| Self::Modulo)),
        (100, Box::new(|_| Self::Eval)),
      ];
      frequency(g, input)
    }
  }
  impl Arbitrary for TagKind {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Self>)> = vec![
        (100, Box::new(|g| TagKind::Expr(Arbitrary::arbitrary(g)))),
        (100, Box::new(|g| TagKind::Cont(Arbitrary::arbitrary(g)))),
        (100, Box::new(|g| TagKind::Op1(Arbitrary::arbitrary(g)))),
        (100, Box::new(|g| TagKind::Op2(Arbitrary::arbitrary(g)))),
      ];
      frequency(g, input)
    }
  }

  impl Arbitrary for Tag {
    fn arbitrary(g: &mut Gen) -> Self {
      Tag {
        version: Arbitrary::arbitrary(g),
        field: Arbitrary::arbitrary(g),
        kind: Arbitrary::arbitrary(g),
      }
    }
  }
}

#[cfg(test)]
#[cfg(feature = "test-utils")]
pub mod tests {

  use super::*;

  #[quickcheck]
  fn prop_version_into_u32(v: Version) -> bool {
    let x: u32 = v.into();
    let v2: Version = x.into();
    v2 == v
  }

  #[quickcheck]
  fn prop_version_from_u32(x: u32) -> bool {
    let v: Version = x.into();
    let x2: u32 = v.into();
    x2 == x
  }

  #[quickcheck]
  fn prop_expr_tag_into_u16(t: ExprTag) -> bool {
    let x: u16 = t.into();
    if let Ok(t2) = ExprTag::try_from(x) {
      t2 == t
    }
    else {
      false
    }
  }

  #[quickcheck]
  fn prop_cont_tag_into_u16(t: ContTag) -> bool {
    let x: u16 = t.into();
    if let Ok(t2) = ContTag::try_from(x) {
      t2 == t
    }
    else {
      false
    }
  }

  #[quickcheck]
  fn prop_op1_tag_into_u16(t: Op1) -> bool {
    let x: u16 = t.into();
    if let Ok(t2) = Op1::try_from(x) {
      t2 == t
    }
    else {
      false
    }
  }
  #[quickcheck]
  fn prop_op2_tag_into_u16(t: Op2) -> bool {
    let x: u16 = t.into();
    if let Ok(t2) = Op2::try_from(x) {
      t2 == t
    }
    else {
      false
    }
  }

  #[quickcheck]
  fn prop_tag_kind_into_u16(t: TagKind) -> bool {
    let x: u16 = t.into();
    if let Ok(t2) = TagKind::try_from(x) {
      t2 == t
    }
    else {
      false
    }
  }

  #[quickcheck]
  fn prop_field_kind_into_u16(f: FieldKind) -> bool {
    let x: u16 = f.into();
    if let Ok(f2) = FieldKind::try_from(x) {
      f2 == f
    }
    else {
      false
    }
  }

  #[quickcheck]
  fn prop_tag_into_u64(t: Tag) -> bool {
    let x: u64 = t.into();
    if let Ok(t2) = Tag::try_from(x) {
      t2 == t
    }
    else {
      false
    }
  }
}
