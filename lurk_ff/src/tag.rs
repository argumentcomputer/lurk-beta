use std::convert::TryFrom;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Tag {
    pub version: Version, // u32
    pub field: FieldKind, // u16
    pub kind: TagKind,    // u16
}

impl Into<u64> for Tag {
    fn into(self) -> u64 {
        let v: u32 = self.version.into();
        let t: u16 = self.kind.into();
        ((v as u64) << 32) + ((self.field as u64) << 16) + (t as u64)
    }
}

impl TryFrom<u64> for Tag {
    type Error = String;

    fn try_from(f: u64) -> Result<Self, Self::Error> {
        let version = Version::from((f >> 32) as u32);
        let field = FieldKind::try_from(((f & 0xffff_0000) >> 16) as u16)?;
        let kind = TagKind::try_from((f & 0xffff) as u16)?;
        Ok(Tag {
            version,
            field,
            kind,
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum FieldKind {
    BLS12_381 = 0b0000_0000_0000_0000,
    Pallas,
    Vesta,
}

impl Into<u16> for FieldKind {
    fn into(self) -> u16 {
        self as u16
    }
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

impl Into<u32> for Version {
    fn into(self) -> u32 {
        ((self.major as u32) << 16) + ((self.minor as u32) << 8) + (self.patch as u32)
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
    Op1(Op1Tag),
    Op2(Op2Tag),
}

impl Into<u16> for TagKind {
    fn into(self) -> u16 {
        match self {
            Self::Expr(x) => x as u16,
            Self::Cont(x) => x as u16,
            Self::Op1(x) => x as u16,
            Self::Op2(x) => x as u16,
        }
    }
}

impl TryFrom<u16> for TagKind {
    type Error = String;

    fn try_from(f: u16) -> Result<Self, Self::Error> {
        if let Ok(x) = ExprTag::try_from(f) {
            Ok(TagKind::Expr(x))
        } else if let Ok(x) = ContTag::try_from(f) {
            Ok(TagKind::Cont(x))
        } else if let Ok(x) = Op1Tag::try_from(f) {
            Ok(TagKind::Op1(x))
        } else if let Ok(x) = Op2Tag::try_from(f) {
            Ok(TagKind::Op2(x))
        } else {
            Err(format!("Invalid TagKind value: {}", f))
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum ExprTag {
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

impl Into<u16> for ExprTag {
    fn into(self) -> u16 {
        self as u16
    }
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

impl Into<u16> for ContTag {
    fn into(self) -> u16 {
        self as u16
    }
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
pub enum Op1Tag {
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

impl Into<u16> for Op1Tag {
    fn into(self) -> u16 {
        self as u16
    }
}

impl TryFrom<u16> for Op1Tag {
    type Error = String;

    fn try_from(x: u16) -> Result<Self, Self::Error> {
        match x {
            x if x == Op1Tag::Car as u16 => Ok(Op1Tag::Car),
            x if x == Op1Tag::Cdr as u16 => Ok(Op1Tag::Cdr),
            x if x == Op1Tag::Atom as u16 => Ok(Op1Tag::Atom),
            x if x == Op1Tag::Emit as u16 => Ok(Op1Tag::Emit),
            x if x == Op1Tag::Open as u16 => Ok(Op1Tag::Open),
            x if x == Op1Tag::Secret as u16 => Ok(Op1Tag::Secret),
            x if x == Op1Tag::Commit as u16 => Ok(Op1Tag::Commit),
            x if x == Op1Tag::Num as u16 => Ok(Op1Tag::Num),
            x if x == Op1Tag::Comm as u16 => Ok(Op1Tag::Comm),
            x if x == Op1Tag::Char as u16 => Ok(Op1Tag::Char),
            x if x == Op1Tag::Eval as u16 => Ok(Op1Tag::Eval),
            x if x == Op1Tag::U64 as u16 => Ok(Op1Tag::U64),
            x => Err(format!("Invalid Op1Tag value: {}", x)),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
#[repr(u16)]
pub enum Op2Tag {
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

impl Into<u16> for Op2Tag {
    fn into(self) -> u16 {
        self as u16
    }
}

impl TryFrom<u16> for Op2Tag {
    type Error = String;

    fn try_from(x: u16) -> Result<Self, Self::Error> {
        match x {
            x if x == Op2Tag::Sum as u16 => Ok(Op2Tag::Sum),
            x if x == Op2Tag::Diff as u16 => Ok(Op2Tag::Diff),
            x if x == Op2Tag::Product as u16 => Ok(Op2Tag::Product),
            x if x == Op2Tag::Quotient as u16 => Ok(Op2Tag::Quotient),
            x if x == Op2Tag::Equal as u16 => Ok(Op2Tag::Equal),
            x if x == Op2Tag::NumEqual as u16 => Ok(Op2Tag::NumEqual),
            x if x == Op2Tag::Less as u16 => Ok(Op2Tag::Less),
            x if x == Op2Tag::Greater as u16 => Ok(Op2Tag::Greater),
            x if x == Op2Tag::LessEqual as u16 => Ok(Op2Tag::LessEqual),
            x if x == Op2Tag::GreaterEqual as u16 => Ok(Op2Tag::GreaterEqual),
            x if x == Op2Tag::Cons as u16 => Ok(Op2Tag::Cons),
            x if x == Op2Tag::StrCons as u16 => Ok(Op2Tag::StrCons),
            x if x == Op2Tag::Begin as u16 => Ok(Op2Tag::Begin),
            x if x == Op2Tag::Hide as u16 => Ok(Op2Tag::Hide),
            x if x == Op2Tag::Modulo as u16 => Ok(Op2Tag::Modulo),
            x if x == Op2Tag::Eval as u16 => Ok(Op2Tag::Eval),
            x => Err(format!("Invalid Op2Tag value: {}", x)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::frequency;
    use quickcheck::{Arbitrary, Gen};

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
    impl Arbitrary for Op1Tag {
        fn arbitrary(g: &mut Gen) -> Self {
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
    impl Arbitrary for Op2Tag {
        fn arbitrary(g: &mut Gen) -> Self {
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
        } else {
            false
        }
    }

    #[quickcheck]
    fn prop_cont_tag_into_u16(t: ContTag) -> bool {
        let x: u16 = t.into();
        if let Ok(t2) = ContTag::try_from(x) {
            t2 == t
        } else {
            false
        }
    }

    #[quickcheck]
    fn prop_op1_tag_into_u16(t: Op1Tag) -> bool {
        let x: u16 = t.into();
        if let Ok(t2) = Op1Tag::try_from(x) {
            t2 == t
        } else {
            false
        }
    }
    #[quickcheck]
    fn prop_op2_tag_into_u16(t: Op2Tag) -> bool {
        let x: u16 = t.into();
        if let Ok(t2) = Op2Tag::try_from(x) {
            t2 == t
        } else {
            false
        }
    }

    #[quickcheck]
    fn prop_tag_kind_into_u16(t: TagKind) -> bool {
        let x: u16 = t.into();
        if let Ok(t2) = TagKind::try_from(x) {
            t2 == t
        } else {
            false
        }
    }

    #[quickcheck]
    fn prop_field_kind_into_u16(f: FieldKind) -> bool {
        let x: u16 = f.into();
        if let Ok(f2) = FieldKind::try_from(x) {
            f2 == f
        } else {
            false
        }
    }

    #[quickcheck]
    fn prop_tag_into_u64(t: Tag) -> bool {
        let x: u64 = t.into();
        if let Ok(t2) = Tag::try_from(x) {
            t2 == t
        } else {
            false
        }
    }
}
