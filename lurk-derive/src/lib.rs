//! Derive macros for Lurk
//! This crate contains derive macros to manage trait dispatch in Lurk.
//!
//! - The `Coproc` macro adds dispatching `Coprocessor` and `Cocircuit` implementaitons to enums whose variants all
//!   atomically enclose types implementing `Coprocessor`.

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
        impl <F: crate::field::LurkField> crate::coprocessor::Coprocessor<F> for #name<F> {
            fn eval_arity(&self) -> usize {
                match self {
                    #eval_arity_arms
                }
            }

            fn evaluate(&self, s: &mut crate::store::Store<F>, args: crate::ptr::Ptr<F>, env: crate::ptr::Ptr<F>, cont: crate::ptr::ContPtr<F>) -> crate::eval::IO<F> {
                match self {
                    #evaluate_arms
                }
            }

            fn simple_evaluate(&self, s: &mut crate::store::Store<F>, args: &[crate::ptr::Ptr<F>]) -> crate::ptr::Ptr<F> {
                match self {
                    #simple_evaluate_arms
                }
            }
        }

        impl<F: crate::field::LurkField> crate::coprocessor::CoCircuit<F> for #name<F> {
            fn arity(&self) -> usize {
                match self {
                    #arity_arms
                }
            }

            fn synthesize<CS: bellperson::ConstraintSystem<F>>(
                &self,
                cs: &mut CS,
                store: &crate::store::Store<F>,
                input_exprs: &[crate::circuit::gadgets::pointer::AllocatedPtr<F>],
                input_env: &crate::circuit::gadgets::pointer::AllocatedPtr<F>,
                input_cont: &crate::circuit::gadgets::pointer::AllocatedContPtr<F>,
            ) -> Result<(crate::circuit::gadgets::pointer::AllocatedPtr<F>, crate::circuit::gadgets::pointer::AllocatedPtr<F>, crate::circuit::gadgets::pointer::AllocatedContPtr<F>), bellperson::SynthesisError> {
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
            #name::#variant_ident(cocircuit) => cocircuit.synthesize(cs, store, input_exprs, input_env, input_cont),
        });
    }
    match_arms
}
