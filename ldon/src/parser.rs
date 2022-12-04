//pub mod base;
//pub mod error;
//pub mod string;
//pub mod syntax;
pub mod position;

use nom_locate::LocatedSpan;

pub type Span<'a> = LocatedSpan<&'a str>;
