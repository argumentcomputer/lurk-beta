// use lurk_ff::field::LurkField;
// use nom::{
//  branch::alt,
//  bytes::complete::{
//    tag,
//    take_till,
//    take_till1,
//  },
//  character::complete::{
//    digit1,
//    multispace0,
//    multispace1,
//    satisfy,
//  },
//  combinator::{
//    eof,
//    map,
//    opt,
//    peek,
//    success,
//    value,
//  },
//  error::context,
//  multi::{
//    many0,
//    many1,
//    separated_list0,
//    separated_list1,
//  },
//  sequence::{
//    delimited,
//    preceded,
//    terminated,
//  },
//  Err,
//  IResult,
//  Parser,
//};
// use crate::{
//  parser::{
//    error::ParseError,
//    Span,
//  },
//  syntax::Syn,
//};
// pub fn parse_line_comment(i: Span) -> IResult<Span, Span, ParseError<Span>> {
//  let (i, _) = tag("//")(i)?;
//  let (i, com) = take_till(|c| c == '\n')(i)?;
//  Ok((i, com))
//}
// pub fn parse_space(i: Span) -> IResult<Span, Vec<Span>, ParseError<Span>> {
//  let (i, _) = multispace0(i)?;
//  let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
//  Ok((i, com))
//}
// pub fn parse_space1(i: Span) -> IResult<Span, Vec<Span>, ParseError<Span>> {
//  let (i, _) = multispace1(i)?;
//  let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
//  Ok((i, com))
//}
// pub fn is_sym_terminator(x: char) -> bool {
//  char::is_whitespace(x)
//    | (x == ')')
//    | (x == '(')
//    | (x == '{')
//    | (x == '}')
//    | (x == '.')
//}
// pub fn parse_sym_limb<'a, F: LurkField>(
//) -> impl Fn(Span<'a>) -> IResult<Span<'a>, String, ParseError<Span<'a>>> {
//  move |from: Span| {
//    let (i, _) = tag(".")(from)?;
//    let (i, s) = take_till1(is_sym_terminator)(i)?;
//    let s: String = String::from(s.fragment().to_owned());
//    Ok((i, s))
//  }
//}
//
//// pub fn parse_raw_sym<'a, F: LurkField>(
//// ) -> impl Fn(Span<'a>) -> IResult<Span<'a>, String, ParseError<Span<'a>>> {
////  move |from: Span| {
////    let (i, _) = tag(".")(from)?;
////    let (i, s) = take_till1(is_sym_terminator)(i)?;
////    let s: String = String::from(s.fragment().to_owned());
////    Ok((i, s))
////  }
//// }
//
//#[cfg(test)]
// pub mod tests {
//  use blstrs::Scalar as Fr;
//
//  use super::*;
//
//  //    #[test]
//}
