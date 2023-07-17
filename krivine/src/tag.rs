use anyhow::anyhow;
use lurk::field::LurkField;

#[derive(Debug, Clone, Copy)]
#[repr(u16)]
pub enum Tag {
    Var,
    Lam,
    App,
    Env,
    Closure,
}

impl Tag {
    pub fn to_field<F: LurkField>(&self) -> F {
        F::from(*self as u64)
    }
}

impl From<Tag> for u16 {
    fn from(val: Tag) -> Self {
        val as u16
    }
}

impl From<Tag> for u64 {
    fn from(val: Tag) -> Self {
        val as u64
    }
}

impl TryFrom<u16> for Tag {
    type Error = anyhow::Error;

    fn try_from(x: u16) -> Result<Self, <Tag as TryFrom<u16>>::Error> {
        match x {
            f if f == Tag::Var as u16 => Ok(Tag::Var),
            f if f == Tag::Lam as u16 => Ok(Tag::Lam),
            f if f == Tag::App as u16 => Ok(Tag::App),
            f => Err(anyhow!("Invalid Tag value: {}", f)),
        }
    }
}
