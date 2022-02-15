//! Lurk DSL
//!
//! We would like to be able to construct data in a natural way from Rust. This
//! will essentially allow bypassing the string-based reader. The Lurk AST is
//! just Lurk data. This module provides a syntax allowing for natural
//! construction of Lurk data embedded in Rust programs. Even if it has no other
//! benefit, this simplifies code formatting and inline editing of embedded
//! Lurk.

extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;

#[derive(Debug)]
enum Lurk {
    Src(String),
}

impl Lurk {
    fn parse_raw(input: proc_macro2::TokenStream) -> Result<Self, syn::Error> {
        // We just immediately turn the `TokenStream` into a string then delegate
        // to the Lurk parser. Although this is a little silly, it is simple.
        let string = input.to_string();
        let mut input_it = input.into_iter().peekable();
        while input_it.next().is_some() {}

        Ok(Lurk::Src(string))
    }

    fn emit(&self) -> TokenStream {
        let output = match self {
            Lurk::Src(string) => {
                quote!(s_.read(&#string))
            }
        };

        output.into()
    }
}

#[proc_macro]
/// Binds a mutable `Store` to the variable `s_`, which is (somewhat unfortunately) hard-coded into the `lurk!` macro.
/// Users should therefore avoid using `s_` for other purposes, and will need to use `s_` directly when manipulating the
/// `Store`. The name `s_` was chosen to walk the line between obscurity and brevity/clarity. Accidental collisions are
/// undesirable, but so is an awkward or unwieldy name.
pub fn let_store(_tokens: TokenStream) -> TokenStream {
    quote!(let mut s_ = Store::<Fr>::default();).into()
}

#[proc_macro]
pub fn lurk(tokens: TokenStream) -> TokenStream {
    Lurk::parse_raw(tokens.into()).unwrap().emit()
}
