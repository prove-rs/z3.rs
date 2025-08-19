use proc_macro::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Attribute, FnArg, ImplItem, ImplItemFn, ItemFn, Pat, PatType, Path, Signature,
    parse_macro_input, spanned::Spanned,
};

/// Usage:
///     #[z3(my_ctx_fn)]
/// where `my_ctx_fn` is a zero-arg function/path you can call like `my_ctx_fn()`.
/// This will always be `Context::thread_local`
#[proc_macro_attribute]
pub fn z3(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Attribute is a callable path, e.g. `Context::default_ctx`
    let default_ctx_fn = parse_macro_input!(attr as Path);

    // Try impl method first; fall back to free fn.
    let ts = item.clone();
    if let Ok(method) = syn::parse::<ImplItemFn>(ts.clone()) {
        return transform_impl_method(default_ctx_fn, method).into();
    }
    let func = parse_macro_input!(item as ItemFn);
    transform_free_fn(default_ctx_fn, func).into()
}

fn transform_impl_method(default_ctx_fn: Path, m: ImplItemFn) -> proc_macro2::TokenStream {
    let orig_ident = m.sig.ident.clone();
    let renamed_ident = format_ident!("{}_in_ctx", orig_ident, span = orig_ident.span());

    let (attrs_for_inner, attrs_for_outer) = split_attrs(&m.attrs, "z3");

    // First non-receiver arg is treated as the context
    let (ctx_index, _ctx_pat, _rest_args) =
        extract_ctx_and_args(&m.sig).unwrap_or_else(|e| abort(m.sig.span(), &e));

    let mut inner_sig = m.sig.clone();
    inner_sig.ident = renamed_ident.clone();

    let mut outer_sig = m.sig.clone();
    remove_nth_nonreceiver_arg(&mut outer_sig, ctx_index);

    let has_receiver = has_receiver(&m.sig);
    let call_target = if has_receiver {
        quote!(self.#renamed_ident)
    } else {
        quote!(Self::#renamed_ident)
    };

    let call_args = build_call_args_calling_fn(&m.sig, ctx_index, &default_ctx_fn);

    let vis = &m.vis;
    let inner_method = ImplItem::Fn(ImplItemFn {
        attrs: attrs_for_inner,
        vis: vis.clone(),
        defaultness: m.defaultness,
        sig: inner_sig,
        block: m.block,
    });

    let outer_block = quote!({ #call_target(#(#call_args),*) });
    let outer_method = ImplItem::Fn(ImplItemFn {
        attrs: attrs_for_outer,
        vis: vis.clone(),
        defaultness: m.defaultness,
        sig: outer_sig,
        block: syn::parse_quote!(#outer_block),
    });

    quote!(#inner_method #outer_method)
}

fn transform_free_fn(default_ctx_fn: Path, f: ItemFn) -> proc_macro2::TokenStream {
    let orig_ident = f.sig.ident.clone();
    let renamed_ident = format_ident!("{}_in_ctx", orig_ident, span = orig_ident.span());

    let (attrs_for_inner, attrs_for_outer) = split_attrs(&f.attrs, "z3");

    let (ctx_index, _ctx_pat, _rest_args) =
        extract_ctx_and_args(&f.sig).unwrap_or_else(|e| abort(f.sig.span(), &e));

    let mut inner_sig = f.sig.clone();
    inner_sig.ident = renamed_ident.clone();

    let mut outer_sig = f.sig.clone();
    remove_nth_nonreceiver_arg(&mut outer_sig, ctx_index);

    let call_args = build_call_args_calling_fn(&f.sig, ctx_index, &default_ctx_fn);

    let vis = &f.vis;
    let inner = ItemFn {
        attrs: attrs_for_inner,
        vis: vis.clone(),
        sig: inner_sig,
        block: f.block,
    };

    let outer_block = quote!({ #renamed_ident(#(#call_args),*) });
    let outer = ItemFn {
        attrs: attrs_for_outer,
        vis: vis.clone(),
        sig: outer_sig,
        block: Box::new(syn::parse_quote!(#outer_block)),
    };

    quote!(#inner #outer)
}

// ---------------- utilities ----------------

fn split_attrs(attrs: &[Attribute], name: &str) -> (Vec<Attribute>, Vec<Attribute>) {
    let mut inner = Vec::new();
    let mut outer = Vec::new();
    for a in attrs {
        if a.path().is_ident(name) {
            // drop our own attr
        } else {
            inner.push(a.clone());
            outer.push(a.clone());
        }
    }
    (inner, outer)
}

fn has_receiver(sig: &Signature) -> bool {
    sig.receiver().is_some()
}

fn extract_ctx_and_args(sig: &Signature) -> Result<(usize, Pat, Vec<Pat>), String> {
    for (i, arg) in sig.inputs.iter().enumerate() {
        if matches!(arg, FnArg::Receiver(_)) {
            continue;
        }
        if let FnArg::Typed(PatType { pat, .. }) = arg {
            return Ok((
                index_of_nonreceiver(sig, i),
                (*pat.as_ref()).clone(),
                collect_pats(sig),
            ));
        } else {
            return Err("Unsupported function arg pattern".into());
        }
    }
    Err("Expected at least one non-receiver argument for context".into())
}

fn index_of_nonreceiver(sig: &Signature, abs_idx: usize) -> usize {
    let mut count = 0usize;
    for (i, arg) in sig.inputs.iter().enumerate() {
        if matches!(arg, FnArg::Receiver(_)) {
            continue;
        }
        if i == abs_idx {
            return count;
        }
        count += 1;
    }
    0
}

fn collect_pats(sig: &Signature) -> Vec<Pat> {
    sig.inputs
        .iter()
        .filter_map(|a| match a {
            FnArg::Receiver(_) => None,
            FnArg::Typed(PatType { pat, .. }) => Some((**pat).clone()),
        })
        .collect()
}

fn remove_nth_nonreceiver_arg(sig: &mut Signature, n: usize) {
    let mut k = 0usize;
    let mut to_remove: Option<usize> = None;
    for (i, arg) in sig.inputs.iter().enumerate() {
        if matches!(arg, FnArg::Receiver(_)) {
            continue;
        }
        if k == n {
            to_remove = Some(i);
            break;
        }
        k += 1;
    }
    if let Some(i) = to_remove {
        let mut new_inputs = syn::punctuated::Punctuated::<FnArg, syn::token::Comma>::new();
        for (j, pair) in sig.inputs.clone().into_pairs().enumerate() {
            if j == i {
                continue;
            }
            let v = pair.into_value();
            new_inputs.push(v)
            // punctuation will be reinserted by pretty printer; no need to manage commas perfectly
        }
        sig.inputs = new_inputs;
    }
}

fn build_call_args_calling_fn(
    sig: &Signature,
    ctx_index: usize,
    default_ctx_fn: &Path,
) -> Vec<proc_macro2::TokenStream> {
    // Pass all non-receiver args, but at the ctx slot, call the provided function.
    let mut args: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut k = 0usize;
    for arg in sig.inputs.iter() {
        match arg {
            FnArg::Receiver(_) => {}
            FnArg::Typed(PatType { pat, .. }) => {
                if k == ctx_index {
                    args.push(quote!(&#default_ctx_fn()));
                } else {
                    args.push(pat.to_token_stream());
                }
                k += 1;
            }
        }
    }
    args
}

fn abort<T: Spanned>(span: T, msg: &str) -> ! {
    let m = syn::LitStr::new(msg, span.span());
    let ts = quote! { compile_error!(#m); };
    // proc-macro abort with a compile_error! at the right span
    panic!("{}", ts.to_string());
}
