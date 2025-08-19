use proc_macro::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::punctuated::Punctuated;
use syn::{
    Attribute, FnArg, ImplItem, ImplItemFn, Item, ItemImpl, PatType, Path, Signature, Type,
    parse_macro_input, spanned::Spanned,
};

/// This macro is used to transform methods in an impl block (or individual function) to
/// rewrite functions that take a `&Context` argument
/// into two functions:
/// * The original, which is renamed to `<original_name>_in_ctx` and keeps its original signature.
/// * A new function, which is named `<original_name>` and has the context argument removed.
///   The implementation of the new method calls the original function, passing
///   the context argument as a call to the provided `default_ctx_fn`.
///
/// In all usage in the z3 crate, the `default_ctx_fn` is `Context::default_ctx`, so you will
/// see [z3(Context::default_ctx)] on many impl blocks and functions.
#[proc_macro_attribute]
pub fn z3(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Attribute is a callable path, e.g. `Context::default_ctx`
    let default_ctx_fn = parse_macro_input!(attr as Path);

    let ts = item.clone();
    // We support running on impl blocks overall, in which we search
    // for methods that take a context and apply to all of them (except wrap)
    // or on individual functions inside impl blocks, in which case we
    // just process the one.
    if let Ok(block) = syn::parse::<ItemImpl>(ts.clone()) {
        // we successfully parsed an impl block, so process
        // all the fns inside it
        return handle_impl(default_ctx_fn, block);
    } else if let Ok(f) = syn::parse::<ImplItemFn>(ts.clone()) {
        // we successfully parsed a fn, so process it
        return handle_fn(default_ctx_fn, f);
    } else if let Ok(item) = syn::parse::<Item>(ts.clone()) {
        // we parsed anythign else, so tell the user not to use the macro
        // on that.
        abort(
            item.span(),
            "This macro can only be applied to impl blocks or methods",
        );
    }

    // We shouldn't reach here.
    abort(quote! {compile_error!()}, "Unable to parse provided item");
}

/// To handle an impl block, we:
/// * Copy all the existing things about the block except for its items
/// * For each item:
///   * If it is not a function, copy it as is
///   * If it is a function, check if it has a context argument (any arg with type `&Context`):
///     * If it does not, copy it as is
///     * If it does, run the function transformation on it (see [`transform_impl_method`]) and insert
///       the two resulting items into the impl block.
/// * Return the modified impl block.
fn handle_impl(default_ctx_fn: Path, block: ItemImpl) -> TokenStream {
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
fn handle_fn(default_ctx_fn: Path, i: ImplItemFn) -> TokenStream {
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

    let attrs = strip_attrs(&m.attrs, "z3");

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
        attrs: attrs.clone(),
        vis: m.vis.clone(),
        defaultness: m.defaultness,
        sig: inner_sig,
        block: m.block,
    });

    // construct the outer method call
    let outer_block = quote!({ #call_target(#(#call_args),*) });
    // construct the full outer method syntax
    let outer_method = ImplItem::Fn(ImplItemFn {
        attrs: attrs.clone(),
        vis: m.vis.clone(),
        defaultness: m.defaultness,
        sig: outer_sig,
        block: syn::parse_quote!(#outer_block),
    });
    (inner_method, outer_method)
}

// ---------------- utilities ----------------

/// Collects the attributes applied to a function and strips out the one
/// specified by `name`
fn strip_attrs(attrs: &[Attribute], name: &str) -> Vec<Attribute> {
    attrs
        .iter()
        .filter(|a| a.path().is_ident(name))
        .cloned()
        .collect()
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

fn abort<T: Spanned>(span: T, msg: &str) -> ! {
    let m = syn::LitStr::new(msg, span.span());
    let ts = quote! { compile_error!(#m); };
    // proc-macro abort with a compile_error! at the right span
    panic!("{}", ts.to_string());
}
