use crate::parser::Span;

/// Source code position of an expression in a file
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pos {
  No,
  Pos {
    from_offset: usize,
    from_line: usize,
    from_column: usize,
    upto_offset: usize,
    upto_line: usize,
    upto_column: usize,
  },
}

impl Pos {
  /// Use the range information in a Position to pretty-print that range within
  /// a string
  pub fn range(
    input: String,
    from_line: usize,
    from_column: usize,
    upto_line: usize,
    upto_column: usize,
  ) -> String {
    let mut res = String::new();
    let gutter = format!("{}", upto_line).len();
    let pad = format!("{: >gutter$}", from_line, gutter = gutter).len()
      + 3
      + from_column;
    res.push_str(&format!("{}▼\n", " ".to_owned().repeat(pad)));
    for (line_number, line) in input.lines().enumerate() {
      if ((line_number + 1) >= from_line) && ((line_number + 1) <= upto_line) {
        res.push_str(&format!(
          "{: >gutter$} | {}\n",
          line_number + 1,
          line,
          gutter = gutter
        ));
      }
    }
    let pad = format!("{: >gutter$}", upto_line, gutter = gutter).len()
      + 3
      + upto_column;
    res.push_str(&format!("{}▲", " ".to_owned().repeat(pad)));
    res
  }

  /// Construct a position from the difference of two Spans
  pub fn from_upto(from: Span, upto: Span) -> Self {
    Self::Pos {
      from_offset: from.location_offset(),
      from_line: from.location_line() as usize,
      from_column: from.get_utf8_column(),
      upto_offset: (upto.location_offset()),
      upto_line: upto.location_line() as usize,
      upto_column: upto.get_utf8_column(),
    }
  }
}

// impl fmt::Display for Position {
//    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//        write!(
//            f,
//            "{}@{}:{}-{}:{}",
//            self.input, self.from_line, self.from_column, self.upto_line,
// self.upto_column        )
//    }
//}

#[cfg(test)]
pub mod tests {
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  impl Arbitrary for Pos {
    fn arbitrary(g: &mut Gen) -> Self {
      Self::Pos {
        from_offset: Arbitrary::arbitrary(g),
        from_line: Arbitrary::arbitrary(g),
        from_column: Arbitrary::arbitrary(g),
        upto_offset: Arbitrary::arbitrary(g),
        upto_line: Arbitrary::arbitrary(g),
        upto_column: Arbitrary::arbitrary(g),
      }
    }
  }
}
