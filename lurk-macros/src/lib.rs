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
use proc_macro2::Span;
use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, AttributeArgs, Data, DataEnum, DeriveInput, Ident, Item, Lit, Meta,
    MetaList, NestedMeta, Path, Type,
};

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
    let has_circuit_arms = has_circuit_match_arms(name, variants);

    let arity_arms = arity_match_arms(name, variants);
    let synthesize_arms = synthesize_match_arms(name, variants);

    let from_impls = from_impls(name, variants);

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

            fn has_circuit(&self) -> bool {
                match self {
                    #has_circuit_arms
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

        #from_impls
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

fn has_circuit_match_arms(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;

        match_arms.extend(quote! {
            #name::#variant_ident(coprocessor) => coprocessor.has_circuit(),
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

fn from_impls(name: &Ident, variants: &DataEnum) -> proc_macro2::TokenStream {
    let mut impls = quote! {};

    for variant in variants.variants.iter() {
        let variant_ident = &variant.ident;
        let variant_inner = match &variant.fields {
            syn::Fields::Unnamed(x) => &x.unnamed,
            _ => unimplemented!(),
        };
        impls.extend(quote! {
            impl<F: lurk::field::LurkField> From<#variant_inner> for #name<F> {
                fn from(c: #variant_inner) -> Self {
                    Self::#variant_ident(c)
                 }
            }
        })
    }

    impls
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

/// This macro is used to generate round-trip serialization tests.
///
/// By appending `serde_test` to a struct or enum definition, you automatically derive
/// serialization tests that employ Serde for round-trip testing. The procedure in the generated tests is:
/// 1. Instantiate the type being tested
/// 2. Serialize the instance, ensuring the operation's success
/// 3. Deserialize the serialized data, comparing the resulting instance with the original one
///
/// The type being tested must meet the following requirements:
/// * Implementations of `Debug` and `PartialEq` traits
/// * Implementation of `Arbitrary` trait
/// * Implementations of `Serialize` and `DeserializeOwned` traits
///
/// For testing generic types, use the `types(...)` attribute to list type parameters for testing,
/// separated by commas. For complex types (e.g., ones where type parameters have their own parameters),
/// enclose them in quotation marks. To test different combinations of type parameters, `types`
/// can be used multiple times.
///
/// # Example
/// ```
/// use proptest_derive::Arbitrary;
/// use serde::{Serialize, Deserialize};
/// use lurk_macros::serde_test;
///
/// // The macro derives serialization tests using an arbitrary instance.
/// #[serde_test(types(u64, "Vec<u64>"), types(u32, bool))]
/// #[derive(Debug, Default, PartialEq, Arbitrary, Serialize, Deserialize)]
/// struct Generic<T1, T2> {
///     t1: T1,
///     t2: T2,
/// }
/// ```
///
#[proc_macro_attribute]
pub fn serde_test(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as AttributeArgs);
    let input = parse_macro_input!(input as Item);
    let name = match &input {
        Item::Struct(item) => &item.ident,
        Item::Enum(item) => &item.ident,
        _ => panic!("This macro only works on structs and enums"),
    };

    // Parse arguments.
    let mut types = Vec::new();
    let mut test_zdata = false;
    for arg in args {
        match arg {
            // List arguments (as in #[serde_test(arg(val))])
            NestedMeta::Meta(Meta::List(MetaList { path, nested, .. })) => match path.get_ident() {
                Some(id) if *id == "types" => {
                    let params = nested.iter().map(parse_type).collect::<Vec<_>>();
                    types.push(quote!(<#name<#(#params),*>>));
                }

                Some(id) if *id == "zdata" => {
                    if nested.len() != 1 {
                        panic!("zdata attribute takes 1 argument");
                    }
                    match &nested[0] {
                        NestedMeta::Lit(Lit::Bool(b)) => {
                            test_zdata = b.value;
                        }
                        _ => panic!("zdata argument must be a boolean"),
                    }
                }

                _ => panic!("invalid attribute {:?}", path),
            },

            _ => panic!("invalid argument {:?}", arg),
        }
    }

    if types.is_empty() {
        // If no explicit type parameters were given for us to test with, assume the type under test
        // takes no type parameters.
        types.push(quote!(<#name>));
    }

    let mut output = quote! {
        #input
    };

    for (i, ty) in types.into_iter().enumerate() {
        let serde_test = {
            let test_name = Ident::new(
                &format!("test_serde_roundtrip_{}_{}", name, i),
                Span::mixed_site(),
            );
            quote! {
                #[cfg(test)]
                proptest::proptest!{
                    #[test]
                    fn #test_name(obj in proptest::prelude::any::#ty()) {
                        let buf = bincode::serialize(&obj).unwrap();
                        assert_eq!(obj, bincode::deserialize(&buf).unwrap());
                    }
                }
            }
        };

        let zdata_test = if test_zdata {
            let test_name = Ident::new(
                &format!("test_zdata_roundtrip_{}_{}", name, i),
                Span::mixed_site(),
            );
            quote! {
                #[cfg(test)]
                proptest::proptest!{
                    #[test]
                    fn #test_name(obj in proptest::prelude::any::#ty()) {
                        let ser = crate::z_data::to_z_data(&obj).unwrap();
                        assert_eq!(obj, crate::z_data::from_z_data(&ser).unwrap());
                    }
                }
            }
        } else {
            quote! {}
        };

        output = quote! {
            #output
            #serde_test
            #zdata_test
        };
    }

    output.into()
}

fn parse_type(m: &NestedMeta) -> Type {
    match m {
        NestedMeta::Lit(Lit::Str(s)) => syn::parse_str(&s.value()).unwrap(),
        NestedMeta::Meta(Meta::Path(p)) => syn::parse2(p.to_token_stream()).unwrap(),
        _ => {
            panic!("expected type");
        }
    }
}

fn try_from_match_arms(
    name: &Ident,
    variant_names: &[&Ident],
    ty: syn::Path,
) -> proc_macro2::TokenStream {
    let mut match_arms = quote! {};
    for variant in variant_names {
        match_arms.extend(quote! {
            x if x == #name::#variant as #ty => Ok(#name::#variant),
        });
    }
    match_arms
}

fn get_type_from_attrs(attrs: &[syn::Attribute], attr_name: &str) -> syn::Result<Path> {
    let Some(nested_arg) = attrs.iter().find_map(|arg| {
        let Ok(Meta::List(MetaList { path, nested, .. })) = arg.parse_meta() else {
            return None;
        };
        if !path.is_ident(attr_name) {
            return None;
        }
        nested.first().cloned()
    }) else {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("Could not find attribute {}", attr_name),
        ));
    };

    match nested_arg {
        NestedMeta::Meta(Meta::Path(path)) => Ok(path),
        bad => Err(syn::Error::new_spanned(
            bad,
            &format!("Could not parse {} attribute", attr_name)[..],
        )),
    }
}

/// This macro derives an impl of TryFrom<foo> for an enum type T with `#[repr(foo)]`.
///
/// # Example
/// ```
/// use lurk_macros::TryFromRepr;
///
/// #[derive(TryFromRepr)]
/// #[repr(u8)]
/// enum Foo {
///     Bar = 0,
///     Baz
/// }
/// ```
///
/// This will derive the natural impl that compares the input representation type to
/// the automatic conversions of each variant into that representation type.
#[proc_macro_derive(TryFromRepr)]
pub fn derive_try_from_repr(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let res_ty = get_type_from_attrs(&ast.attrs, "repr");

    let name = &ast.ident;
    let variants = match ast.data {
        Data::Enum(ref variants) => variants
            .variants
            .iter()
            .map(|v| &v.ident)
            .collect::<Vec<_>>(),
        Data::Struct(_) | Data::Union(_) => {
            panic!("#[derive(TryFromRepr)] is only defined for enums")
        }
    };

    match res_ty {
        Err(e) => {
            // If no explicit repr were given for us, we can't pursue
            panic!(
                "TryFromRepr macro requires a repr parameter, which couldn't be parsed: {:?}",
                e
            );
        }
        Ok(ty) => {
            let match_arms = try_from_match_arms(name, &variants, ty.clone());
            let name_str = name.to_string();
            quote! {
                impl std::convert::TryFrom<#ty> for #name {
                    type Error = anyhow::Error;
                    fn try_from(v: #ty) -> Result<Self, <Self as TryFrom<#ty>>::Error> {
                        match v {
                            #match_arms
                            _ => Err(anyhow::anyhow!("invalid variant for enum {}", #name_str)),
                        }
                    }
                }
            }
        }
    }
    .into()
}
