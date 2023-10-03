use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse2, parse_macro_input, Attribute, Item, ItemFn, ItemMod};

pub fn generic_tests(_args: TokenStream, input: TokenStream) -> TokenStream {
    let mut test_mod: ItemMod = parse_macro_input!(input);
    let name = &test_mod.ident;

    test_mod.content.as_mut().map(|(brace, items)| {
        let macro_name = format_ident!("instantiate_{}", name);

        let macro_body: proc_macro2::TokenStream = items
            .iter_mut()
            .filter_map(|item| {
                if let Item::Fn(f) = item {
                    let test_attrs = take_test_attrs(f);
                    if test_attrs.is_empty() {
                        return None;
                    }

                    let mut test_sig = f.sig.clone();
                    test_sig.generics = Default::default();
                    let test_name = &test_sig.ident;
                    let call = quote!(#name::#test_name::<$($t),*>());

                    Some(quote! {
                        #(#test_attrs)*
                        #test_sig {
                            #call
                        }
                    })
                } else {
                    None
                }
            })
            .collect();

        items.push(
            parse2(quote! {
                #[macro_export]
                macro_rules! #macro_name {
                    ($($t:ty),*) => {
                        #macro_body
                    };
                }
            })
            .expect("Failed to parse the macro rule"),
        );

        (brace, items.clone())
    });

    quote! {
        #[macro_use]
        #test_mod
    }
    .into()
}

fn take_test_attrs(f: &mut ItemFn) -> Vec<Attribute> {
    let mut test_attrs = Vec::new();
    f.attrs.retain(|attr| {
        if is_test_attr(attr) {
            test_attrs.push(attr.clone());
            false
        } else {
            true
        }
    });
    test_attrs
}

fn is_test_attr(attr: &Attribute) -> bool {
    attr.path.segments.last().map_or(false, |segment| {
        matches!(
            segment.ident.to_string().as_str(),
            "test" | "ignore" | "bench" | "should_panic"
        )
    })
}
