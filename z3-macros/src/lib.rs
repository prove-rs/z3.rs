use proc_macro::TokenStream;
use quote::quote;
use syn::spanned::Spanned;
use syn::{Block, ImplItemFn, Item, ItemImpl, Path, parse_macro_input, ImplItem, ItemForeignMod};

mod default_ctx;
mod non_null;

/// This macro is used to transform methods in an impl block (or individual function) to
/// rewrite functions that take a `&Context` argument
/// into two functions:
/// * The original, which is renamed to `<original_name>_in_ctx` and keeps its original signature.
/// * A new function, which is named `<original_name>` and has the context argument removed.
///   The implementation of the new method calls the original function, passing
///   the context argument as a call to the provided `default_ctx_fn`.
///
/// In all usage in the z3 crate, the `default_ctx_fn` is `Context::default_ctx`, so you will
/// see [z3_ctx(Context::default_ctx)] on many impl blocks and functions.
#[proc_macro_attribute]
pub fn z3_ctx(attr: TokenStream, item: TokenStream) -> TokenStream {
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
        return crate::default_ctx::handle_impl(default_ctx_fn, block);
    } else if let Ok(f) = syn::parse::<ImplItemFn>(ts.clone()) {
        // we successfully parsed a fn, so process it
        return crate::default_ctx::handle_fn(default_ctx_fn, f);
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

/// This macro is used to transform methods in an impl block (or individual function) to
/// rewrite functions that take a `&Context` argument
/// into two functions:
/// * The original, which is renamed to `<original_name>_in_ctx` and keeps its original signature.
/// * A new function, which is named `<original_name>` and has the context argument removed.
///   The implementation of the new method calls the original function, passing
///   the context argument as a call to the provided `default_ctx_fn`.
///
/// In all usage in the z3 crate, the `default_ctx_fn` is `Context::default_ctx`, so you will
/// see [z3_ctx(Context::default_ctx)] on many impl blocks and functions.
#[proc_macro_attribute]
pub fn z3_non_null(_: TokenStream, item: TokenStream) -> TokenStream {
    let ts = item.clone();
    if let Ok(block) = syn::parse::<ItemForeignMod>(ts.clone()) {
        // we successfully parsed an impl block, so process
        // all the fns inside it
        return non_null::handle_impl(block);
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
// ---------------- utilities ----------------

fn abort<T: Spanned>(span: T, msg: &str) -> ! {
    let m = syn::LitStr::new(msg, span.span());
    let ts = quote! { compile_error!(#m); };
    // proc-macro abort with a compile_error! at the right span
    panic!("{}", ts.to_string());
}
