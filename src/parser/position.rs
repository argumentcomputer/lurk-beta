use crate::parser::Span;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

/// Source code position of an expression in a file
#[derive(Clone, Copy, Debug)]
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

// This is so we can easily use derive(PartialEq) on datatypes like `Syntax` which contain `Pos`,
// since the source position an AST node comes from doesn't effect its equality
impl PartialEq for Pos {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for Pos {}

#[cfg(not(target_arch = "wasm32"))]
impl Arbitrary for Pos {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        any::<()>().prop_map(|_| Pos::No).boxed()
    }
}

impl Pos {
    /// Use the range information in a Position to pretty-print that range within
    /// a string
    pub fn range(
        input: &str,
        from_line: usize,
        from_column: usize,
        upto_line: usize,
        upto_column: usize,
    ) -> String {
        let mut res = String::new();
        let gutter = format!("{upto_line}").len();
        let pad = format!("{from_line: >gutter$}").len() + 3 + from_column;
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
        let pad = format!("{upto_line: >gutter$}").len() + 3 + upto_column;
        res.push_str(&format!("{}▲", " ".to_owned().repeat(pad)));
        res
    }

    /// Construct a position from the difference of two Spans
    pub fn from_upto(from: Span<'_>, upto: Span<'_>) -> Self {
        Self::Pos {
            from_offset: from.location_offset(),
            from_line: from.location_line() as usize,
            from_column: from.get_utf8_column(),
            upto_offset: (upto.location_offset()),
            upto_line: upto.location_line() as usize,
            upto_column: upto.get_utf8_column(),
        }
    }

    /// Retrieves the `from_offset` attribute, if present
    pub fn get_from_offset(&self) -> Option<usize> {
        match self {
            Self::No => None,
            Self::Pos { from_offset, .. } => Some(*from_offset),
        }
    }
}
