use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DeriveInput, Fields, parse_macro_input};

/// Visit identity-bearing fields; derived serialization's transient fields stay transient.
#[proc_macro_derive(Relocate, attributes(relocate))]
pub fn derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let mut generics = input.generics.clone();
    for param in generics.type_params_mut() {
        param.bounds.push(syn::parse_quote!(artifact::Relocate));
        param.bounds.push(syn::parse_quote!('static));
    }
    let (implementation, arguments, clause) = generics.split_for_impl();
    let skip = |field: &syn::Field| {
        field.attrs.iter().any(|attr| {
            if !attr.path().is_ident("serde") && !attr.path().is_ident("relocate") {
                return false;
            }
            let mut skip = false;
            let _ = attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("skip") {
                    skip = true;
                }
                if meta.input.peek(syn::Token![=]) {
                    let _: syn::Expr = meta.value()?.parse()?;
                }
                Ok(())
            });
            skip
        })
    };
    let visit = |fields: &Fields| {
        fields
            .iter()
            .enumerate()
            .filter(|(_, f)| !skip(f))
            .map(|(index, field)| {
                let member = field
                    .ident
                    .clone()
                    .map(syn::Member::Named)
                    .unwrap_or(syn::Member::Unnamed(index.into()));
                quote!(artifact::Relocate::relocate(&mut self.#member, relocation)?;)
            })
            .collect::<Vec<_>>()
    };
    let body = match &input.data {
        Data::Struct(data) => {
            let fields = visit(&data.fields);
            quote!(#(#fields)*)
        }
        Data::Enum(data) => {
            let arms = data.variants.iter().map(|variant| {
                let tag = &variant.ident;
                let bindings: Vec<_> = variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| {
                        f.ident
                            .clone()
                            .unwrap_or_else(|| format_ident!("field_{i}"))
                    })
                    .collect();
                let visits = variant
                    .fields
                    .iter()
                    .zip(&bindings)
                    .filter(|(f, _)| !skip(f))
                    .map(
                        |(_, binding)| quote!(artifact::Relocate::relocate(#binding, relocation)?;),
                    );
                let pattern = match &variant.fields {
                    Fields::Named(_) => quote!({#(#bindings),*}),
                    Fields::Unnamed(_) => quote!((#(#bindings),*)),
                    Fields::Unit => quote!(),
                };
                quote!(Self::#tag #pattern => { #(#visits)* })
            });
            quote!(match self { #(#arms),* })
        }
        Data::Union(_) => {
            return syn::Error::new_spanned(name, "unions cannot be relocated")
                .to_compile_error()
                .into();
        }
    };
    quote! {
        impl #implementation artifact::Relocate for #name #arguments #clause {
            fn relocate(&mut self, relocation: &mut artifact::Relocation) -> artifact::Result<()> {
                #body
                Ok(())
            }
        }
    }
    .into()
}
