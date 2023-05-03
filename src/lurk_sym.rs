
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
pub enum LurkSym {
  Nil,
  T,
  If,
  Lambda,
  Let,
  LetRec,
  Quote,
  Atom,
  Functionp,
  Cons,
  StrCons,
  Car,
  Cdr,
  Num,
  Char,
  Eq,
  CurrentEnv,
  Eval,
  Comm,
  Commit,
  Hide,
  Open,



}
