use lurk_ff::field::LurkField;
use nom::{
  branch::alt,
  bytes::complete::{
    tag,
    take_till,
    take_till1,
  },
  character::complete::{
    digit1,
    multispace0,
    multispace1,
    satisfy,
  },
  combinator::{
    eof,
    map,
    opt,
    peek,
    success,
    value,
  },
  error::context,
  multi::{
    many0,
    many1,
    separated_list0,
    separated_list1,
  },
  sequence::{
    delimited,
    preceded,
    terminated,
  },
  Err,
  IResult,
};

use crate::{
  parser::{
    base,
    error::{
      ParseError,
      ParseErrorKind,
    },
    position::Pos,
    string,
    Span,
  },
  syntax::Syn,
};
pub fn parse_line_comment<F: LurkField>(
  i: Span,
) -> IResult<Span, Span, ParseError<Span, F>> {
  let (i, _) = tag("//")(i)?;
  let (i, com) = take_till(|c| c == '\n')(i)?;
  Ok((i, com))
}
pub fn parse_space<F: LurkField>(
  i: Span,
) -> IResult<Span, Vec<Span>, ParseError<Span, F>> {
  let (i, _) = multispace0(i)?;
  let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
  Ok((i, com))
}
pub fn parse_space1<F: LurkField>(
  i: Span,
) -> IResult<Span, Vec<Span>, ParseError<Span, F>> {
  let (i, _) = multispace1(i)?;
  let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
  Ok((i, com))
}
pub fn is_sym_terminator(x: char) -> bool {
  char::is_whitespace(x)
    | (x == ')')
    | (x == '(')
    | (x == '{')
    | (x == '}')
    | (x == ',')
}

pub fn parse_syn_sym_root<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (upto, is_key) =
      alt((value(true, tag("_:")), value(false, tag("_"))))(from)?;
    let pos = Pos::from_upto(from, upto);
    if is_key {
      Ok((upto, Syn::Keyword(pos, vec![])))
    }
    else {
      Ok((upto, Syn::Symbol(pos, vec![])))
    }
  }
}

pub fn parse_symkey_limb<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, String, ParseError<Span, F>> {
  move |from: Span| {
    let (i, s) = take_till(|x| is_sym_terminator(x) || x == '.')(from)?;
    let s: String = String::from(s.fragment().to_owned());
    Ok((i, s))
  }
}

pub fn parse_syn_sym<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, is_key) =
      alt((value(false, tag(".")), value(true, tag(":"))))(from)?;
    let (i, root_limb) = parse_symkey_limb()(i)?;
    let (upto, rest) = many0(preceded(tag("."), parse_symkey_limb()))(i)?;
    let mut limbs: Vec<String> = vec![root_limb];
    limbs.extend(rest);
    let pos = Pos::from_upto(from, upto);
    if is_key {
      Ok((upto, Syn::Keyword(pos, limbs)))
    }
    else {
      Ok((upto, Syn::Symbol(pos, limbs)))
    }
  }
}

pub fn parse_syn_u64<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, base) = alt((
      preceded(tag("0"), base::parse_litbase_code()),
      success(base::LitBase::Dec),
    ))(from)?;
    let (i, digits) = base::parse_litbase_digits(base)(i)?;
    // when more uint types are supported we can do:
    // alt((tag("u8"), tag("u16"), tag("u32"), tag("u64"), tag("u128")))
    let (upto, suffix) = tag("u64")(i)?;
    match *suffix.fragment() {
      "u64" => {
        let (_, x) = ParseError::res(
          u64::from_str_radix(&digits, base.radix()),
          from,
          |e| ParseErrorKind::ParseIntErr(e),
        )?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syn::U64(pos, x)))
      },
      _ => unreachable!("implementation error in parse_nat"),
    }
  }
}

pub fn parse_syn_num<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, base) = alt((
      preceded(tag("0"), base::parse_litbase_code()),
      success(base::LitBase::Dec),
    ))(from)?;
    let (upto, bytes): (Span, Vec<u8>) = base::parse_litbase_le_bytes(base)(i)?;
    let max_bytes = (F::zero() - F::one()).to_le_bytes();
    let max_uint = num_bigint::BigUint::from_bytes_le(&max_bytes);
    if num_bigint::BigUint::from_bytes_le(&bytes) > max_uint {
      return ParseError::throw(
        from,
        ParseErrorKind::NumLiteralTooBig(F::most_positive(), max_uint),
      );
    }
    else {
      let pos = Pos::from_upto(from, upto);
      Ok((upto, Syn::Num(pos, F::from_le_bytes(&bytes))))
    }
  }
}

pub fn parse_syn_str<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (upto, s) = string::parse_string('"')(from)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::String(pos, s)))
  }
}

pub fn parse_syn_char<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (upto, mut s) = string::parse_string('\'')(from)?;
    if s.len() == 1 {
      let c = s.pop().unwrap();
      let pos = Pos::from_upto(from, upto);
      Ok((upto, Syn::Char(pos, c)))
    }
    else {
      ParseError::throw(from, ParseErrorKind::InvalidChar(s.clone()))
    }
  }
}

pub fn parse_syn_list_improper<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("(")(from)?;
    let (i, mut xs) = separated_list1(
      preceded(parse_space, tag(",")),
      preceded(parse_space, parse_syn()),
    )(i)?;
    let (upto, _) = preceded(parse_space, tag(")"))(i)?;
    let end = xs.pop();
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::List(pos, xs, end.map(Box::new))))
  }
}

pub fn parse_syn_list_proper<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("(")(from)?;
    let (i, xs) = many0(preceded(parse_space, parse_syn()))(i)?;
    let (upto, _) = preceded(parse_space, tag(")"))(i)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::List(pos, xs, None)))
  }
}

pub fn parse_syn_map_entry<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, (Syn<F>, Syn<F>), ParseError<Span, F>> {
  move |from: Span| {
    let (i, key) = parse_syn()(from)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, val) = parse_syn()(i)?;
    Ok((i, (key, val)))
  }
}

pub fn parse_syn_map<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("{")(from)?;
    let (i, xs) = separated_list1(
      preceded(parse_space, tag(",")),
      preceded(parse_space, parse_syn_map_entry()),
    )(i)?;
    let (upto, _) = preceded(parse_space, tag("}"))(i)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::Map(pos, xs)))
  }
}

pub fn parse_syn<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    alt((
      parse_syn_sym_root(),
      parse_syn_sym(),
      parse_syn_str(),
      parse_syn_list_improper(),
      parse_syn_list_proper(),
      parse_syn_map(),
    ))(from)
  }
}

#[cfg(test)]
pub mod tests {
  use blstrs::Scalar as Fr;
  use lurk_ff::field::test_utils::FWrap;
  use nom::Parser;

  use super::*;

  fn test_parse<'a, P>(mut p: P, i: &'a str, expected: Option<Syn<Fr>>)
  where P: Parser<Span<'a>, Syn<Fr>, ParseError<Span<'a>, Fr>> {
    match (expected, p.parse(Span::new(i))) {
      (Some(expected), Ok((i, x))) if x == expected => (),
      (Some(expected), Ok((i, x))) => {
        println!("input: {:?}", i);
        println!("expected: {:?}", expected);
        println!("detected: {:?}", x);
        assert!(false)
      },
      (Some(..), Err(e)) => {
        println!("{}", e);
        assert!(false)
      },
      (None, Ok((i, x))) => {
        println!("input: {:?}", i);
        println!("expected parse error");
        println!("detected: {:?}", x);
        assert!(false)
      },
      (None, Err(e)) => (),
    }
  }

  #[test]
  fn unit_parse_string() {
    test_parse(
      parse_syn_str(),
      "\"foo\"",
      Some(Syn::String(Pos::No, String::from("foo"))),
    );
    test_parse(
      parse_syn_str(),
      "\"fo\\no\"",
      Some(Syn::String(Pos::No, String::from("fo\no"))),
    );
    test_parse(
      parse_syn_str(),
      "\"fo\\u{00}o\"",
      Some(Syn::String(Pos::No, String::from("fo\u{00}o"))),
    );
    test_parse(
      parse_syn_str(),
      "\"foo\\    \"",
      Some(Syn::String(Pos::No, String::from("foo"))),
    );
  }

  #[test]
  fn unit_parse_symbol() {
    test_parse(parse_syn_sym_root(), "_", Some(Syn::Symbol(Pos::No, vec![])));
    test_parse(
      parse_syn_sym(),
      ".foo",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string()])),
    );
    test_parse(
      parse_syn(),
      ".foo",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      "..foo",
      Some(Syn::Symbol(Pos::No, vec!["".to_string(), "foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ".foo.bar",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string(), "bar".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ".foo?.bar?",
      Some(Syn::Symbol(Pos::No, vec!["foo?".to_string(), "bar?".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ".fooλ.barλ",
      Some(Syn::Symbol(Pos::No, vec!["fooλ".to_string(), "barλ".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ".foo.:bar",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string(), ":bar".to_string()])),
    );
  }

  #[test]
  fn unit_parse_keyword() {
    test_parse(parse_syn_sym_root(), "_:", Some(Syn::Keyword(Pos::No, vec![])));
    test_parse(
      parse_syn_sym(),
      ":foo",
      Some(Syn::Keyword(Pos::No, vec!["foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ":foo.bar",
      Some(Syn::Keyword(Pos::No, vec!["foo".to_string(), "bar".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ":foo?.bar?",
      Some(Syn::Keyword(Pos::No, vec!["foo?".to_string(), "bar?".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ":fooλ.barλ",
      Some(Syn::Keyword(Pos::No, vec!["fooλ".to_string(), "barλ".to_string()])),
    );
  }

  #[test]
  fn unit_parse_list() {
    test_parse(
      parse_syn_list_improper(),
      "(.a, .b)",
      Some(Syn::List(
        Pos::No,
        vec![Syn::Symbol(Pos::No, vec!["a".to_string()])],
        Some(Box::new(Syn::Symbol(Pos::No, vec!["b".to_string()]))),
      )),
    );
    test_parse(
      parse_syn_list_proper(),
      "(.a .b)",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Symbol(Pos::No, vec!["a".to_string()]),
          Syn::Symbol(Pos::No, vec!["b".to_string()]),
        ],
        None,
      )),
    );

    test_parse(
      parse_syn_list_proper(),
      "(.a .b .c)",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Symbol(Pos::No, vec!["a".to_string()]),
          Syn::Symbol(Pos::No, vec!["b".to_string()]),
          Syn::Symbol(Pos::No, vec!["c".to_string()]),
        ],
        None,
      )),
    );

    test_parse(
      parse_syn_list_improper(),
      "(.a, .b, .c)",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Symbol(Pos::No, vec!["a".to_string()]),
          Syn::Symbol(Pos::No, vec!["b".to_string()]),
        ],
        Some(Box::new(Syn::Symbol(Pos::No, vec!["c".to_string()]))),
      )),
    );
  }

  #[test]
  fn unit_parse_num() {
    test_parse(parse_syn_num(), "0", Some(Syn::Num(Pos::No, 0u64.into())));
    test_parse(parse_syn_num(), "0b0", Some(Syn::Num(Pos::No, 0u64.into())));
    test_parse(parse_syn_num(), "0o0", Some(Syn::Num(Pos::No, 0u64.into())));
    test_parse(parse_syn_num(), "0d0", Some(Syn::Num(Pos::No, 0u64.into())));
    test_parse(parse_syn_num(), "0x0", Some(Syn::Num(Pos::No, 0u64.into())));
    test_parse(
      parse_syn_num(),
      "0xffffffffffffffff",
      Some(Syn::Num(Pos::No, 0xffffffffffffffffu64.into())),
    );
    test_parse(
      parse_syn_num(),
      "0x1234_5678_9abc_def0",
      Some(Syn::Num(Pos::No, 0x1234_5678_9abc_def0u64.into())),
    );
    test_parse(
      parse_syn_num(),
      &format!("0x{}", Fr::most_positive().hex_digits()),
      Some(Syn::Num(Pos::No, Fr::most_positive())),
    );
    test_parse(
      parse_syn_num(),
      "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000",
      Some(Syn::Num(Pos::No, <Fr as ff::Field>::zero() - Fr::from(1u64))),
    );
    test_parse(
      parse_syn_num(),
      "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
      None,
    );
  }

  #[quickcheck]
  fn prop_parse_num(f: FWrap<Fr>) -> bool {
    let hex = format!("0x{}", f.0.hex_digits());
    match parse_syn_num::<Fr>()(Span::new(&hex)) {
      Ok((_, Syn::Num(_, f2))) => {
        println!("f1 0x{}", f.0.hex_digits());
        println!("f2 0x{}", f2.hex_digits());
        f.0 == f2
      },
      _ => false,
    }
  }
}
