//! # Lurk Macros
//!
//! ## Derive macros for Lurk
//!
//! This crate contains derive macros to manage trait dispatch in Lurk.
//!
//! - The `Coproc` macro adds dispatching `Coprocessor` and `Cocircuit` implementations to enums whose variants all
//!   atomically enclose types implementing `Coprocessor`.
//!
//! ## Lurk macro
//!
//! Although severely limited in the expressions it can represent, and still lacking quasiquoting,
//! the `lurk` macro allows embedding Lurk code in Rust source. See tests for examples.

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DataEnum, DeriveInput, Ident};

#[proc_macro_derive(Coproc)]
pub fn derive_enum_coproc(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);

    let name = &ast.ident;
    match ast.data {
        Data::Enum(ref variants) => impl_enum_coproc(name, variants),
        Data::Struct(_) | Data::Union(_) => panic!("#[derive(Coproc)] is only defined for enums"),
    }
}

fn impl_enum_coproc(name: &Ident, variants: &DataEnum) -> TokenStream {
    let eval_arity_arms = eval_arity_match_arms(name, variants);
    let evaluate_arms = evaluate_match_arms(name, variants);
    let simple_evaluate_arms = simple_evaluate_match_arms(name, variants);

    let arity_arms = arity_match_arms(name, variants);
    let synthesize_arms = synthesize_match_arms(name, variants);
    let res = quote! {
        impl <F: lurk::field::LurkField> lurk::coprocessor::Coprocessor<F> for #name<F> {
            fn eval_arity(&self) -> usize {
                match self {
                    #eval_arity_arms
                }
            }

            fn evaluate(&self, s: &mut lurk::store::Store<F>, args: lurk::ptr::Ptr<F>, env: lurk::ptr::Ptr<F>, cont: lurk::ptr::ContPtr<F>) -> lurk::eval::IO<F> {
                match self {
                    #evaluate_arms
                }
            }

            fn simple_evaluate(&self, s: &mut lurk::store::Store<F>, args: &[lurk::ptr::Ptr<F>]) -> lurk::ptr::Ptr<F> {
                match self {
                    #simple_evaluate_arms
                }
            }
        }

        impl<F: lurk::field::LurkField> lurk::coprocessor::CoCircuit<F> for #name<F> {
            fn arity(&self) -> usize {
                match self {
                    #arity_arms
                }
            }

            fn synthesize<CS: bellperson::ConstraintSystem<F>>(
                &self,
                cs: &mut CS,
                g: &lurk::circuit::gadgets::data::GlobalAllocations<F>,
                store: &lurk::store::Store<F>,
                input_exprs: &[lurk::circuit::gadgets::pointer::AllocatedPtr<F>],
                input_env: &lurk::circuit::gadgets::pointer::AllocatedPtr<F>,
                input_cont: &lurk::circuit::gadgets::pointer::AllocatedContPtr<F>,
            ) -> Result<(lurk::circuit::gadgets::pointer::AllocatedPtr<F>, lurk::circuit::gadgets::pointer::AllocatedPtr<F>, lurk::circuit::gadgets::pointer::AllocatedContPtr<F>), bellperson::SynthesisError> {
                match self {
                    #synthesize_arms
                }
            }
        }
    };
    res.into()
}

fn eval_arity_match_arms(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;

        match_arms.extend(quote! {
            #name::#variant_ident(coprocessor) => coprocessor.eval_arity(),
        });
    }
    match_arms
}

fn evaluate_match_arms(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;

        match_arms.extend(quote! {
            #name::#variant_ident(coprocessor) => coprocessor.evaluate(s, args, env, cont),
        });
    }
    match_arms
}

fn simple_evaluate_match_arms(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;

        match_arms.extend(quote! {
            #name::#variant_ident(coprocessor) => coprocessor.simple_evaluate(s, args),
        });
    }
    match_arms
}

fn arity_match_arms(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;

        match_arms.extend(quote! {
            #name::#variant_ident(cocircuit) => cocircuit.arity(),
        });
    }
    match_arms
}

fn synthesize_match_arms(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;

        match_arms.extend(quote! {
            #name::#variant_ident(cocircuit) => cocircuit.synthesize(cs, g, store, input_exprs, input_env, input_cont),
        });
    }
    match_arms
}

////////////////////////////////////////////////////////////////////////////////
// Lurk Macro

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
    quote!(let s_ = &mut Store::<Fr>::default();).into()
}

#[proc_macro]
pub fn lurk(tokens: TokenStream) -> TokenStream {
    Lurk::parse_raw(tokens.into()).unwrap().emit()
}
