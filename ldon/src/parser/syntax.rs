use lurk_ff::field::LurkField;
use nom::{
  branch::alt,
  bytes::complete::{
    tag,
    take_till,
  },
  character::complete::{
    char,
    multispace0,
    multispace1,
    none_of,
  },
  combinator::{
    peek,
    success,
    value,
  },
  multi::{
    many0,
    separated_list0,
    separated_list1,
  },
  sequence::{
    preceded,
    terminated,
  },
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

pub fn parse_syn_symnil<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (upto, tag) = alt((tag("_:"), tag("_.")))(from)?;
    let pos = Pos::from_upto(from, upto);
    if *tag.fragment() == "_." {
      Ok((upto, Syn::Symbol(pos, vec![])))
    }
    else {
      Ok((upto, Syn::Keyword(pos, vec![])))
    }
  }
}

pub fn parse_syn_sym<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, root) =
      alt((char('.'), char(':'), value('.', peek(none_of(",=(){}[]")))))(from)?;
    let (upto, limbs) = separated_list1(
      char(root),
      string::parse_string_inner(root, false, ".:,=(){}[]"),
    )(i)?;
    // println!("limbs {:?}", limbs);
    let pos = Pos::from_upto(from, upto);
    if root == ':' {
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
    let max_bytes = (F::zero() - F::one()).to_le_bytes_noncanonical();
    let max_uint = num_bigint::BigUint::from_bytes_le(&max_bytes);
    if num_bigint::BigUint::from_bytes_le(&bytes) > max_uint {
      return ParseError::throw(
        from,
        ParseErrorKind::NumLiteralTooBig(F::most_positive(), max_uint),
      );
    }
    else {
      let pos = Pos::from_upto(from, upto);
      Ok((upto, Syn::Num(pos, F::from_le_bytes_noncanonical(&bytes))))
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
    let (upto, s) = string::parse_string('\'')(from)?;
    let mut chars: Vec<char> = s.chars().collect();
    if chars.len() == 1 {
      let c = chars.pop().unwrap();
      let pos = Pos::from_upto(from, upto);
      Ok((upto, Syn::Char(pos, c)))
    }
    else {
      ParseError::throw(from, ParseErrorKind::InvalidChar(s.clone()))
    }
  }
}

// (1, 2)
// FIXME: if the end of an improper list is a list, the result is a single list
pub fn parse_syn_list_improper<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("(")(from)?;
    let (i, mut xs) = separated_list1(
      preceded(parse_space, tag(",")),
      preceded(parse_space, parse_syn()),
    )(i)?;
    let (upto, _) = preceded(parse_space, tag(")"))(i)?;
    // separated_list1 is guaranteed to return at least 1 thing
    let end = match xs.pop().unwrap() {
      // if the end is a list, we want to merge it into our current list
      Syn::List(_, end_xs, end_end) => {
        xs.extend(end_xs);
        end_end
      },
      x => Some(Box::new(x)),
    };
    let pos = Pos::from_upto(from, upto);
    // improper lists require at least 2 elements, if this parser gets called
    // on a list of 1 element, return a proper list instead
    match (end, xs.is_empty()) {
      (Some(end), true) => Ok((upto, Syn::List(pos, vec![*end], None))),
      (None, true) => Ok((upto, Syn::List(pos, vec![], None))),
      (end, false) => Ok((upto, Syn::List(pos, xs, end))),
    }
  }
}

pub fn parse_syn_list_proper<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("(")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, xs) = separated_list0(parse_space1, parse_syn())(i)?;
    // println!("list xs {:?}", xs);
    let (upto, _) = tag(")")(i)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::List(pos, xs, None)))
  }
}

pub fn parse_syn_link<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("[")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, ctx) = parse_syn()(i)?;
    let (i, _) = parse_space(i)?;
    let (i, xs) = separated_list0(parse_space1, parse_syn_u64())(i)?;
    let mut xs2 = vec![];
    for x in xs {
      match x {
        Syn::U64(_, x) => xs2.push(x),
        _ => unreachable!(
          "xs should only be generated from a list of Syn from parse_syn_u64"
        ),
      }
    }
    let (upto, _) = tag("]")(i)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::Link(pos, Box::new(ctx), xs2)))
  }
}

pub fn parse_syn_map_entry<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, (Syn<F>, Syn<F>), ParseError<Span, F>> {
  move |from: Span| {
    let (i, key) = parse_syn()(from)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag("=")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, val) = parse_syn()(i)?;
    Ok((i, (key, val)))
  }
}

pub fn parse_syn_map<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    let (i, _) = tag("{")(from)?;
    let (i, xs) = separated_list0(
      preceded(parse_space, tag(",")),
      preceded(parse_space, parse_syn_map_entry()),
    )(i)?;
    let (upto, _) = preceded(parse_space, tag("}"))(i)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, Syn::Map(pos, xs)))
  }
}

// top-level syntax parser
pub fn parse_syn<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, Syn<F>, ParseError<Span, F>> {
  move |from: Span| {
    alt((
      parse_syn_char(),
      parse_syn_str(),
      parse_syn_u64(),
      parse_syn_num(),
      parse_syn_list_proper(),
      parse_syn_list_improper(),
      parse_syn_link(),
      parse_syn_map(),
      parse_syn_symnil(),
      parse_syn_sym(),
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
      (Some(expected), Ok((_i, x))) if x == expected => (),
      (Some(expected), Ok((i, x))) => {
        println!("input: {:?}", i);
        println!("expected: {}", expected);
        println!("detected: {}", x);
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
      (None, Err(_e)) => (),
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
    test_parse(parse_syn_sym(), "", None);
    test_parse(parse_syn(), "_.", Some(Syn::Symbol(Pos::No, vec![])));
    test_parse(
      parse_syn_sym(),
      ".",
      Some(Syn::Symbol(Pos::No, vec!["".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      "..",
      Some(Syn::Symbol(Pos::No, vec!["".to_string(), "".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      "foo",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      "foo",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      "..foo",
      Some(Syn::Symbol(Pos::No, vec!["".to_string(), "foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      "foo.",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string(), "".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ".foo.",
      Some(Syn::Symbol(Pos::No, vec!["foo".to_string(), "".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ".foo..",
      Some(Syn::Symbol(
        Pos::No,
        vec!["foo".to_string(), "".to_string(), "".to_string()],
      )),
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
      ".foo\\n.bar\\n",
      Some(Syn::Symbol(
        Pos::No,
        vec!["foo\n".to_string(), "bar\n".to_string()],
      )),
    );
    test_parse(
      parse_syn_sym(),
      ".foo\\u{00}.bar\\u{00}",
      Some(Syn::Symbol(
        Pos::No,
        vec!["foo\u{00}".to_string(), "bar\u{00}".to_string()],
      )),
    );
    test_parse(
      parse_syn_sym(),
      ".foo\\.bar",
      Some(Syn::Symbol(Pos::No, vec!["foo.bar".to_string()])),
    );
  }

  #[test]
  fn unit_parse_keyword() {
    test_parse(parse_syn(), "_:", Some(Syn::Keyword(Pos::No, vec![])));
    test_parse(
      parse_syn_sym(),
      ":foo",
      Some(Syn::Keyword(Pos::No, vec!["foo".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ":foo:bar",
      Some(Syn::Keyword(Pos::No, vec!["foo".to_string(), "bar".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ":foo?:bar?",
      Some(Syn::Keyword(Pos::No, vec!["foo?".to_string(), "bar?".to_string()])),
    );
    test_parse(
      parse_syn_sym(),
      ":fooλ:barλ",
      Some(Syn::Keyword(Pos::No, vec!["fooλ".to_string(), "barλ".to_string()])),
    );
  }

  #[test]
  fn unit_parse_map() {
    test_parse(parse_syn_map(), "{}", Some(Syn::Map(Pos::No, vec![])));
    test_parse(
      parse_syn_map(),
      "{ 'a' = 1u64,  'b' = 2u64,  'c' = 3u64 }",
      Some(Syn::Map(
        Pos::No,
        vec![
          (Syn::Char(Pos::No, 'a'), Syn::U64(Pos::No, 1)),
          (Syn::Char(Pos::No, 'b'), Syn::U64(Pos::No, 2)),
          (Syn::Char(Pos::No, 'c'), Syn::U64(Pos::No, 3)),
        ],
      )),
    );
    test_parse(
      parse_syn_map(),
      "{ 'a' = 1u64,  'b' = 2u64,  'c' = 3u64 }",
      Some(Syn::Map(
        Pos::No,
        vec![
          (Syn::Char(Pos::No, 'a'), Syn::U64(Pos::No, 1)),
          (Syn::Char(Pos::No, 'b'), Syn::U64(Pos::No, 2)),
          (Syn::Char(Pos::No, 'c'), Syn::U64(Pos::No, 3)),
        ],
      )),
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
      parse_syn_list_improper(),
      "(a, b)",
      Some(Syn::List(
        Pos::No,
        vec![Syn::Symbol(Pos::No, vec!["a".to_string()])],
        Some(Box::new(Syn::Symbol(Pos::No, vec!["b".to_string()]))),
      )),
    );
    test_parse(
      parse_syn_list_proper(),
      "()",
      Some(Syn::List(Pos::No, vec![], None)),
    );
    test_parse(
      parse_syn_list_proper(),
      "(a b)",
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
      parse_syn_list_improper(),
      "(a, (b, c))",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Symbol(Pos::No, vec!["a".to_string()]),
          Syn::Symbol(Pos::No, vec!["b".to_string()]),
        ],
        Some(Box::new(Syn::Symbol(Pos::No, vec!["c".to_string()]))),
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
    test_parse(
      parse_syn_list_proper(),
      "('a' 'b' 'c')",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Char(Pos::No, 'a'),
          Syn::Char(Pos::No, 'b'),
          Syn::Char(Pos::No, 'c'),
        ],
        None,
      )),
    );
    test_parse(
      parse_syn_list_proper(),
      "('a' 'b' 'c')",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Char(Pos::No, 'a'),
          Syn::Char(Pos::No, 'b'),
          Syn::Char(Pos::No, 'c'),
        ],
        None,
      )),
    );
  }
  #[test]
  fn unit_parse_char() {
    test_parse(parse_syn_char(), "'a'", Some(Syn::Char(Pos::No, 'a')));
    test_parse(parse_syn_char(), "'b'", Some(Syn::Char(Pos::No, 'b')));
    test_parse(
      parse_syn_char(),
      "'\\u{8f}'",
      Some(Syn::Char(Pos::No, '\u{8f}')),
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
  #[test]
  fn unit_parse_syn() {
    let vec: Vec<u8> = vec![
      0x6e, 0x2e, 0x50, 0x55, 0xdc, 0xf6, 0x14, 0x86, 0xb0, 0x3b, 0xb8, 0x0e,
      0xd2, 0xb3, 0xf1, 0xa3, 0x5c, 0x30, 0xe1, 0x22, 0xde, 0xfe, 0xba, 0xe8,
      0x24, 0xfa, 0xe4, 0xed, 0x32, 0x40, 0x8e, 0x87,
    ]
    .into_iter()
    .rev()
    .collect();
    test_parse(
      parse_syn(),
      "(0x6e2e5055dcf61486b03bb80ed2b3f1a35c30e122defebae824fae4ed32408e87)",
      Some(Syn::List(
        Pos::No,
        vec![Syn::Num(Pos::No, Fr::from_le_bytes_noncanonical(&vec))],
        None,
      )),
    );
    test_parse(
      parse_syn(),
      ".\\.",
      Some(Syn::Symbol(Pos::No, vec![".".to_string()])),
    );
    test_parse(
      parse_syn(),
      "(lambda (🚀) 🚀)",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Symbol(Pos::No, vec!["lambda".to_string()]),
          Syn::List(
            Pos::No,
            vec![Syn::Symbol(Pos::No, vec!["🚀".to_string()])],
            None,
          ),
          Syn::Symbol(Pos::No, vec!["🚀".to_string()]),
        ],
        None,
      )),
    );
    test_parse(
      parse_syn(),
      ".\\'",
      Some(Syn::Symbol(Pos::No, vec!["'".to_string()])),
    );
    test_parse(
      parse_syn(),
      ".\\'\\u{8e}\\u{fffc}\\u{201b}",
      Some(Syn::Symbol(Pos::No, vec!["'\u{8e}\u{fffc}\u{201b}".to_string()])),
    );
    test_parse(
      parse_syn(),
      "(_:, 11242421860377074631u64, :\u{ae}\u{60500}\u{87}::)",
      Some(Syn::List(
        Pos::No,
        vec![
          Syn::Keyword(Pos::No, vec![]),
          Syn::U64(Pos::No, 11242421860377074631),
        ],
        Some(Box::new(Syn::Keyword(
          Pos::No,
          vec!["®\u{60500}\u{87}".to_string(), "".to_string(), "".to_string()],
        ))),
      )),
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
  #[quickcheck]
  fn prop_syn_parse_print(syn: Syn<Fr>) -> bool {
    println!("==================");
    println!("syn1 {}", syn);
    println!("syn1 {:?}", syn);
    let hex = format!("{}", syn);
    match parse_syn::<Fr>()(Span::new(&hex)) {
      Ok((_, syn2)) => {
        println!("syn2 {}", syn2);
        println!("syn2 {:?}", syn2);
        syn == syn2
      },
      _ => false,
    }
  }
}
