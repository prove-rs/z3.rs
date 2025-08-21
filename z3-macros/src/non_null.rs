use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::{ToTokens, quote};
use syn::parse::Parse;
use syn::punctuated::{Pair, Punctuated};
use syn::token::Comma;
use syn::{Block, FnArg, ForeignItem, ForeignItemFn, ImplItem, Item, ItemForeignMod, ReturnType, Signature, Type, TypePath};

pub(crate) fn handle_impl(block: ItemForeignMod) -> TokenStream {
    let i = ItemForeignMod {
        attrs: block.attrs,
        abi: block.abi,
        unsafety: block.unsafety,
        brace_token: block.brace_token,
        items: process_items(block.items),
    };
    quote! {#i}.into()
}

fn process_items(items: Vec<ForeignItem>) -> Vec<ForeignItem> {
    items.into_iter().map(process_foreign_item).collect()
}

fn process_foreign_item(item: ForeignItem) -> ForeignItem {
    match item {
        ForeignItem::Fn(a) => ForeignItem::Fn(process_foreign_item_fn(a)),
        _ => item,
    }
}

fn process_foreign_item_fn(item: ForeignItemFn) -> ForeignItemFn {
    ForeignItemFn {
        attrs: item.attrs,
        vis: item.vis,
        sig: process_signature(item.sig),
        semi_token: item.semi_token,
    }
}

fn process_signature(item: Signature) -> Signature {
    let mut new_item = item.clone();
    new_item.output = process_type(item.output);
    new_item
}

fn process_type(ret: ReturnType) -> ReturnType {
    match &ret {
        ReturnType::Default => { ret.clone() }
        ReturnType::Type(arrow, a) => {
            match a.as_ref() {
                Type::Path(path) => {
                    if let Some(ident) = path.path.get_ident() {
                        if make_nullable(ident.to_string()) {
                            let t =
                                syn::parse::<Type>(TokenStream::from(quote! { std::option::Option<#ident>}));
                            if let Ok(t) = t {
                                return ReturnType::Type(arrow.clone(), Box::new(t));
                            } else {
                                panic!()
                            }
                        }
                    }
                }
                _ => {}
            }
            ret
        }
    }
}

fn make_nullable<T: AsRef<str>>(t: T) -> bool {
    t.as_ref().contains("Z3_")
}
