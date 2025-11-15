use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{Data, DeriveInput, Fields, GenericParam, WherePredicate, parse_macro_input, parse::{Parse, ParseStream}, Token};

/// Information about the struct for code generation
struct StructInfo {
    named: bool,
    fields: Vec<proc_macro2::TokenStream>,
}

/// Shared helper: validate struct, collect fields, add generic bounds
fn prepare_struct(
    input: DeriveInput,
    bound: syn::Path,
) -> Result<(syn::Ident, syn::Generics, StructInfo), TokenStream> {
    // Add bounds to all type parameters
    let mut input = input;
    let idents: Vec<_> = input
        .generics
        .params
        .iter()
        .filter_map(|param| {
            if let GenericParam::Type(type_param) = param {
                Some(type_param.ident.clone())
            } else {
                None
            }
        })
        .collect();

    let generics = &mut input.generics;
    let where_clause = generics.make_where_clause();
    for ident in idents {
        let predicate: WherePredicate = syn::parse_quote!(#ident: #bound);
        where_clause.predicates.push(predicate);
    }

    let name = input.ident.clone();

    let info = match input.data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => {
                let fields = fields
                    .named
                    .into_iter()
                    .map(|f| f.ident.unwrap())
                    .map(|x| quote!(#x))
                    .collect();
                StructInfo {
                    named: true,
                    fields,
                }
            }
            Fields::Unnamed(fields) => {
                let fields = fields
                    .unnamed
                    .into_iter()
                    .enumerate()
                    .map(|(i, _)| syn::Index::from(i))
                    .map(|x| quote!(#x))
                    .collect();
                StructInfo {
                    named: false,
                    fields,
                }
            }
            Fields::Unit => StructInfo {
                named: true,
                fields: vec![],
            },
        },
        Data::Enum(_) => return Err(quote! { compile_error!("Cannot constant time traits for enums as doing so would require branching on the variant"); }.into()),
        Data::Union(_) => return Err(quote! { compile_error!("Cannot derive for unions"); }.into()),
    };

    Ok((name, input.generics, info))
}

fn crate_ident() -> proc_macro2::TokenStream {
    let crate_name = proc_macro_crate::crate_name("cnti").expect("cnti is in Cargo.toml");
    match crate_name {
        proc_macro_crate::FoundCrate::Itself => quote!(crate),
        proc_macro_crate::FoundCrate::Name(name) => {
            let ident = syn::Ident::new(&name, Span::call_site());
            quote!(#ident)
        }
    }
}

#[proc_macro_derive(CtEq)]
pub fn derive_ct_partial_eq(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let crate_prefix = crate_ident();
    let (name, generics, info) = match prepare_struct(input, syn::parse_quote!(#crate_prefix::CtEq))
    {
        Ok(v) => v,
        Err(ts) => return ts,
    };
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body = if info.fields.is_empty() {
        quote!(#crate_prefix::CtBool::TRUE)
    } else {
        let comparisons = info
            .fields
            .iter()
            .map(|id| quote!(self.#id.ct_eq(&other.#id)));
        quote! {
            #(#comparisons)&*
        }
    };

    quote! {
        impl #impl_generics #crate_prefix::CtEq for #name #ty_generics #where_clause {
            fn ct_eq(&self, other: &Self) -> CtBool {
                use #crate_prefix::CtEq as _;
                #body
            }
        }
    }
    .into()
}

#[proc_macro_derive(CtSelect)]
pub fn derive_ct_select(input: TokenStream) -> TokenStream {
    let crate_prefix = crate_ident();
    let input = parse_macro_input!(input as DeriveInput);
    let (name, generics, info) =
        match prepare_struct(input, syn::parse_quote!(#crate_prefix::CtSelect)) {
            Ok(v) => v,
            Err(ts) => return ts,
        };
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body = if info.fields.is_empty() {
        quote!(Self)
    } else if info.named {
        let assigns = info.fields.iter().map(
            |id| quote!(#id: #crate_prefix::CtSelect::ct_select(choice, &then.#id, &else_.#id)),
        );
        quote!(Self { #(#assigns),* })
    } else {
        let assigns = info
            .fields
            .iter()
            .map(|idx| quote!(#crate_prefix::CtSelect::ct_select(choice, &then.#idx, &else_.#idx)));
        quote!(Self( #(#assigns),* ))
    };

    quote! {
        impl #impl_generics #crate_prefix::CtSelect for #name #ty_generics #where_clause {
            fn ct_select(choice: #crate_prefix::CtBool, then: &Self, else_: &Self) -> Self {
                #body
            }
        }
    }
    .into()
}

#[proc_macro_derive(CtOrd)]
pub fn derive_ct_ord(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let crate_prefix = crate_ident();
    let (name, generics, info) =
        match prepare_struct(input, syn::parse_quote!(#crate_prefix::CtOrd)) {
            Ok(v) => v,
            Err(ts) => return ts,
        };
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body = match info.fields.len() {
        0 => quote! {#crate_prefix::CtBool::FALSE},
        1 => {
            let field = info.fields.into_iter().next().unwrap();
            quote! {self.#field.ct_gt(&other.#field)}
        }
        _ => {
            let mut eq_bindings = Vec::new();
            let mut gt_bindings = Vec::new();
            let mut field_var_names = Vec::new();

            // Create temp variables for each field
            for field in &info.fields {
                let base_name = field.to_string();
                let gt_var = syn::Ident::new(&format!("gt_{}", base_name), Span::call_site());
                let eq_var = syn::Ident::new(&format!("eq_{}", base_name), Span::call_site());

                gt_bindings.push(quote! { let #gt_var = self.#field.ct_gt(&other.#field); });
                eq_bindings.push(quote! { let #eq_var = self.#field.ct_eq(&other.#field); });
                field_var_names.push((eq_var, gt_var));
            }

            // Build lexicographic chain: left-to-right
            let mut iter = field_var_names.into_iter().rev();
            let (_, last_gt) = iter.next().unwrap();
            let mut chained_expr = quote! { #last_gt };

            for (eq_var, gt_var) in iter {
                chained_expr = quote! { #gt_var | (#eq_var & (#chained_expr)) };
            }

            quote! {
                #(#eq_bindings)*
                #(#gt_bindings)*
                #chained_expr
            }
        }
    };

    quote! {
        impl #impl_generics #crate_prefix::CtOrd for #name #ty_generics #where_clause {
            fn ct_gt(&self, other: &Self) -> CtBool {
                use #crate_prefix::CtOrd as _;
                use #crate_prefix::CtEq as _;
                #body
            }
        }
    }
    .into()
}

/// Input parser for tuple_impl! macro
enum TupleImplInput {
    Single(usize),
    Range(usize, usize),
}

impl Parse for TupleImplInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let start: syn::LitInt = input.parse()?;
        let start_val = start.base10_parse::<usize>()?;

        if input.peek(Token![..]) {
            input.parse::<Token![..]>()?;
            let end: syn::LitInt = input.parse()?;
            let end_val = end.base10_parse::<usize>()?;
            Ok(TupleImplInput::Range(start_val, end_val))
        } else {
            Ok(TupleImplInput::Single(start_val))
        }
    }
}

fn generate_tuple_ct_eq_impl(n: usize) -> proc_macro2::TokenStream {
    let crate_prefix = crate_ident();

    // Generate type parameters: T0, T1, T2, ...
    let type_params: Vec<_> = (0..n)
        .map(|i| syn::Ident::new(&format!("T{}", i), Span::call_site()))
        .collect();

    // Generate tuple indices: 0, 1, 2, ...
    let indices: Vec<_> = (0..n).map(syn::Index::from).collect();

    if n == 0 {
        return quote! {
            impl #crate_prefix::CtEq for () {
                #[inline]
                fn ct_eq(&self, _other: &Self) -> #crate_prefix::CtBool {
                    #crate_prefix::CtBool::TRUE
                }
            }
        };
    }

    let body = if n == 1 {
        quote! { self.0.ct_eq(&other.0) }
    } else {
        quote! {
            #(self.#indices.ct_eq(&other.#indices))&*
        }
    };

    quote! {
        impl<#(#type_params: #crate_prefix::CtEq),*> #crate_prefix::CtEq for (#(#type_params,)*) {
            #[inline]
            fn ct_eq(&self, other: &Self) -> #crate_prefix::CtBool {
                use #crate_prefix::CtEq as _;
                #body
            }
        }
    }
}

fn generate_tuple_ct_select_impl(n: usize) -> proc_macro2::TokenStream {
    let crate_prefix = crate_ident();

    let type_params: Vec<_> = (0..n)
        .map(|i| syn::Ident::new(&format!("T{}", i), Span::call_site()))
        .collect();

    let indices: Vec<_> = (0..n).map(syn::Index::from).collect();

    if n == 0 {
        return quote! {
            impl #crate_prefix::CtSelect for () {
                #[inline]
                fn ct_select(_choice: #crate_prefix::CtBool, _then: &Self, _else_: &Self) -> Self {
                    ()
                }
            }
        };
    }

    let selects = indices.iter().map(|idx| {
        quote! { #crate_prefix::CtSelect::ct_select(choice, &then.#idx, &else_.#idx) }
    });

    quote! {
        impl<#(#type_params: #crate_prefix::CtSelect),*> #crate_prefix::CtSelect for (#(#type_params,)*) {
            #[inline]
            fn ct_select(choice: #crate_prefix::CtBool, then: &Self, else_: &Self) -> Self {
                (#(#selects,)*)
            }
        }
    }
}

fn generate_tuple_ct_ord_impl(n: usize) -> proc_macro2::TokenStream {
    let crate_prefix = crate_ident();

    let type_params: Vec<_> = (0..n)
        .map(|i| syn::Ident::new(&format!("T{}", i), Span::call_site()))
        .collect();

    let indices: Vec<_> = (0..n).map(syn::Index::from).collect();

    if n == 0 {
        return quote! {
            impl #crate_prefix::CtOrd for () {
                #[inline]
                fn ct_gt(&self, _other: &Self) -> #crate_prefix::CtBool {
                    #crate_prefix::CtBool::FALSE
                }
            }
        };
    }

    let body = if n == 1 {
        quote! { self.0.ct_gt(&other.0) }
    } else {
        // Generate variable names for each field's gt and eq
        let mut eq_bindings = Vec::new();
        let mut gt_bindings = Vec::new();
        let mut field_var_names = Vec::new();

        for (i, idx) in indices.iter().enumerate() {
            let gt_var = syn::Ident::new(&format!("gt_{}", i), Span::call_site());
            let eq_var = syn::Ident::new(&format!("eq_{}", i), Span::call_site());

            gt_bindings.push(quote! { let #gt_var = self.#idx.ct_gt(&other.#idx); });
            eq_bindings.push(quote! { let #eq_var = self.#idx.ct_eq(&other.#idx); });
            field_var_names.push((eq_var, gt_var));
        }

        // Build lexicographic chain: right to left
        let mut iter = field_var_names.into_iter().rev();
        let (_, last_gt) = iter.next().unwrap();
        let mut chained_expr = quote! { #last_gt };

        for (eq_var, gt_var) in iter {
            chained_expr = quote! { #gt_var | (#eq_var & (#chained_expr)) };
        }

        quote! {
            #(#eq_bindings)*
            #(#gt_bindings)*
            #chained_expr
        }
    };

    quote! {
        impl<#(#type_params: #crate_prefix::CtOrd),*> #crate_prefix::CtOrd for (#(#type_params,)*) {
            #[inline]
            fn ct_gt(&self, other: &Self) -> #crate_prefix::CtBool {
                use #crate_prefix::CtOrd as _;
                use #crate_prefix::CtEq as _;
                #body
            }
        }
    }
}

/// Generates trait implementations for tuples of specified sizes.
///
/// # Usage
///
/// Generate implementations for a single tuple size:
/// ```ignore
/// tuple_impl!(3);  // Generates impls for (T0, T1, T2)
/// ```
///
/// Generate implementations for a range of tuple sizes:
/// ```ignore
/// tuple_impl!(2..5);  // Generates impls for tuples of size 2, 3, and 4
/// ```
///
/// This macro generates implementations of `CtEq`, `CtSelect`, and `CtOrd` for tuples
/// in the same way that deriving these traits on an equivalent tuple struct would.
#[proc_macro]
pub fn tuple_impl(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as TupleImplInput);

    let sizes: Vec<usize> = match input {
        TupleImplInput::Single(n) => vec![n],
        TupleImplInput::Range(start, end) => (start..end).collect(),
    };

    let mut output = proc_macro2::TokenStream::new();

    for size in sizes {
        output.extend(generate_tuple_ct_eq_impl(size));
        output.extend(generate_tuple_ct_select_impl(size));
        output.extend(generate_tuple_ct_ord_impl(size));
    }

    output.into()
}
