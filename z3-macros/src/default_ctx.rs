use proc_macro::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::punctuated::Punctuated;
use syn::{FnArg, ImplItem, ImplItemFn, ItemImpl, PatType, Path, Signature, Type};

/// To handle an impl block, we:
/// * Copy all the existing things about the block except for its items
/// * For each item:
///   * If it is not a function, copy it as is
///   * If it is a function, check if it has a context argument (any arg with type `&Context`):
///     * If it does not, copy it as is
///     * If it does, run the function transformation on it (see [`transform_impl_method`]) and insert
///       the two resulting items into the impl block.
/// * Return the modified impl block.
pub(crate) fn handle_impl(default_ctx_fn: Path, block: ItemImpl) -> TokenStream {
    let mut i = ItemImpl {
        attrs: block.attrs,
        defaultness: block.defaultness,
        unsafety: block.unsafety,
        impl_token: block.impl_token,
        generics: block.generics,
        trait_: block.trait_,
        self_ty: block.self_ty,
        brace_token: block.brace_token,
        items: vec![],
    };
    for x in block.items.iter() {
        if let Ok(f) = syn::parse::<ImplItemFn>(TokenStream::from(x.to_token_stream())) {
            if f.sig.ident != "wrap" && f.sig.inputs.iter().any(is_fn_arg_context) {
                let (a, b) = transform_impl_method(default_ctx_fn.clone(), f);
                i.items.push(a);
                i.items.push(b);
            } else {
                i.items.push(ImplItem::Fn(f.clone()))
            }
        } else {
            i.items.push(x.clone());
        }
    }
    quote!(#i).into()
}

/// To handle a function simply run the function transformation on it
/// and return the two resulting items. See [`transform_impl_method`].
pub(crate) fn handle_fn(default_ctx_fn: Path, i: ImplItemFn) -> TokenStream {
    let (inner, outer) = transform_impl_method(default_ctx_fn.clone(), i);
    quote!(#inner #outer).into()
}

/// Transforms an impl method that takes a context argument into two methods:
/// * The inner method, which is renamed to `<original_name>_in_ctx` and keeps its original signature.
/// * The outer method, which is named `<original_name>` and has the context argument removed.
///   The implementation of the outer method calls the inner method, passing
///   the context argument as a call to the provided `default_ctx_fn`.
fn transform_impl_method(default_ctx_fn: Path, m: ImplItemFn) -> (ImplItem, ImplItem) {
    // original and renamed names
    let orig_ident = m.sig.ident.clone();
    let renamed_ident = format_ident!("{}_in_ctx", orig_ident, span = orig_ident.span());

    // We need to copy the attributes of the original method, so we can use them on both
    // We find the first context argument and use that. Our API is highly regular so there
    // are no cases where there are multiple context arguments.

    let mut inner_sig = m.sig.clone();
    inner_sig.ident = renamed_ident.clone();

    let mut outer_sig = m.sig.clone();
    filter_ctx_args(&mut outer_sig);

    let call_target = if m.sig.receiver().is_some() {
        // don't think this ever happens but just in case
        quote!(self.#renamed_ident)
    } else {
        quote!(Self::#renamed_ident)
    };

    let call_args = build_call_args_calling_fn(&m.sig, &default_ctx_fn);

    // construct the inner method syntax, with the changed signature
    let inner_method = ImplItem::Fn(ImplItemFn {
        attrs: m.attrs.clone(),
        vis: m.vis.clone(),
        defaultness: m.defaultness,
        sig: inner_sig,
        block: m.block,
    });

    // construct the outer method call
    let outer_block = quote!({ #call_target(#(#call_args),*) });

    let mut outer_attrs = m.attrs.clone();
    let msg = format!(
        "This method is a macro-generated wrapper around [`Self::{renamed_ident}`] which automatically provides a default thread_local [`Context`].",
    );
    outer_attrs.push(syn::parse_quote!(#[doc = ""]));
    outer_attrs.push(syn::parse_quote!(
        #[doc = #msg]
    ));

    // construct the full outer method syntax
    let outer_method = ImplItem::Fn(ImplItemFn {
        attrs: outer_attrs.clone(),
        vis: m.vis.clone(),
        defaultness: m.defaultness,
        sig: outer_sig,
        block: syn::parse_quote!(#outer_block),
    });
    (inner_method, outer_method)
}

/// Checks if the provided `arg` is of type `&Context`
fn is_fn_arg_context(arg: &FnArg) -> bool {
    if matches!(arg, FnArg::Receiver(_)) {
        return false;
    }
    if let FnArg::Typed(PatType { ty, .. }) = arg
        && let Type::Reference(r) = ty.as_ref().clone()
        && r.elem.to_token_stream().to_string() == "Context"
    {
        return true;
    }
    false
}

/// Filter in place a fn [`Signature`] to not include a `&Context` argument
fn filter_ctx_args(sig: &mut Signature) {
    let pairs = sig
        .inputs
        .pairs()
        .filter(|pair| !is_fn_arg_context(pair.value()))
        .map(|a| a.cloned());
    sig.inputs = Punctuated::<FnArg, syn::token::Comma>::from_iter(pairs);
}

/// Given a function signature and the index of the context argument inside it,
/// build the syntax of the arguments of a function call to that function with
/// the context argument replaced by a call to the provided `default_ctx_fn`.
fn build_call_args_calling_fn(
    sig: &Signature,
    default_ctx_fn: &Path,
) -> Vec<proc_macro2::TokenStream> {
    // Pass all non-receiver args, replacing any Ctx with the given default-ctx getter.
    sig.inputs
        .iter()
        .flat_map(|arg| {
            if is_fn_arg_context(arg) {
                Some(quote! {&#default_ctx_fn()})
            } else if let FnArg::Typed(PatType { pat, .. }) = arg {
                Some(pat.to_token_stream())
            } else {
                None
            }
        })
        .collect()
}
