//! Transform raw bindgen output into z3-sys–compatible function declarations.
//!
//! Reads bindgen-generated Rust from stdin and writes transformed Rust to stdout.
//!
//! Transformations applied to each `extern "C"` function:
//!
//! **Nullability:** Pointer parameters are left as-is (they use `Z3_X` type
//! aliases, which are `NonNull<_Z3_X>` in the hand-written code). Return types
//! that are Z3 opaque handle types are wrapped in `Option<>`, modeling Z3's
//! null-on-failure convention.
//!
//! **Doc comments:** Doxygen markup is converted to Rust markdown:
//! - `\brief` prefix stripped (text becomes the opening paragraph)
//! - `\param name desc` → `- \`name\`: desc` list items
//! - `\remark text` → `**Remark:** text`
//! - `\note text` → `**Note:** text`
//! - `\pre condition` → collected into a `# Preconditions` section
//! - `\sa Name` → collected into a `# See also` section
//! - `\c word` → `` `word` ``
//! - `\ccode{expr}` → `` `expr` `` (with `\,` unescaped to `,`)
//! - `#Z3_fn()` / `#Z3_fn` → `` [`Z3_fn`] ``
//! - `def_API(...)`, `@name`, `@{`, `@}` lines stripped entirely
//!
//! All `extern "C"` blocks in the input are merged into a single block.

use std::io::Read;

use quote::quote;
use syn::{Attribute, Expr, ExprLit, ForeignItem, ForeignItemFn, Item, Lit, Meta, MetaNameValue,
          ReturnType, Type};

// ---------------------------------------------------------------------------
// Opaque handle type list
// ---------------------------------------------------------------------------

/// Z3 opaque handle types created by the DEFINE_TYPE macro in z3_api.h.
/// Return types matching these names are wrapped in `Option<>`.
const OPAQUE_HANDLE_TYPES: &[&str] = &[
    "Z3_symbol",
    "Z3_literals",
    "Z3_config",
    "Z3_context",
    "Z3_sort",
    "Z3_func_decl",
    "Z3_ast",
    "Z3_app",
    "Z3_pattern",
    "Z3_model",
    "Z3_constructor",
    "Z3_constructor_list",
    "Z3_params",
    "Z3_param_descrs",
    "Z3_parser_context",
    "Z3_goal",
    "Z3_tactic",
    "Z3_simplifier",
    "Z3_probe",
    "Z3_stats",
    "Z3_solver",
    "Z3_solver_callback",
    "Z3_ast_vector",
    "Z3_ast_map",
    "Z3_apply_result",
    "Z3_func_interp",
    "Z3_func_entry",
    "Z3_fixedpoint",
    "Z3_optimize",
    "Z3_rcf_num",
];

fn is_opaque_handle(ty: &Type) -> bool {
    match ty {
        Type::Path(type_path) if type_path.qself.is_none() => type_path
            .path
            .get_ident()
            .is_some_and(|ident| OPAQUE_HANDLE_TYPES.contains(&ident.to_string().as_str())),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Doxygen → Rust doc comment processing
// ---------------------------------------------------------------------------

/// Returns true for lines that should be dropped entirely.
fn is_strip_line(line: &str) -> bool {
    let t = line.trim();
    // `def_API(` or `def_API (` — Z3 API declaration macro, not documentation.
    t.starts_with("def_API")
        // Doxygen group markers: @{, @{*/, @}, @}*/
        || t.starts_with("@{")
        || t.starts_with("@}")
        || t.starts_with("/**@{*/")
        || t.starts_with("/**@}*/")
        || t.starts_with("@name ")
        // C comment opener that leaks in from adjacent group markers:
        // /** @name Group */ /**@{*/ /** \brief ... → after stripping /** and @name,
        // the remaining @{*/ and /** show up as stray lines.
        || t == "/**"
}

/// If the line is a `\sa` directive, extract all referenced names.
fn extract_sa(line: &str) -> Option<Vec<String>> {
    let rest = line.trim().strip_prefix(r"\sa ")?;
    let names: Vec<String> = rest
        .split_whitespace()
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect();
    if names.is_empty() { None } else { Some(names) }
}

/// Replace `\ccode{expr\,with\,commas}` with `` `expr,with,commas` ``.
fn replace_ccode(s: &str) -> String {
    let needle = r"\ccode{";
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(start) = rest.find(needle) {
        out.push_str(&rest[..start]);
        rest = &rest[start + needle.len()..];
        if let Some(end) = rest.find('}') {
            let content = rest[..end].replace(r"\,", ",");
            out.push('`');
            out.push_str(&content);
            out.push('`');
            rest = &rest[end + 1..];
        } else {
            out.push_str(needle); // malformed — keep as-is
        }
    }
    out.push_str(rest);
    out
}

/// Replace `\c word` with `` `word` ``.
fn replace_c_ref(s: &str) -> String {
    let needle = r"\c ";
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(start) = rest.find(needle) {
        out.push_str(&rest[..start]);
        rest = &rest[start + needle.len()..];
        let end = rest
            .find(|c: char| !c.is_alphanumeric() && c != '_' && c != ':')
            .unwrap_or(rest.len());
        out.push('`');
        out.push_str(&rest[..end]);
        out.push('`');
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

/// Replace `#Z3_identifier[()]` with `` [`Z3_identifier`] ``.
fn replace_hash_ref(s: &str) -> String {
    let needle = "#Z3_";
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(start) = rest.find(needle) {
        out.push_str(&rest[..start]);
        rest = &rest[start + 1..]; // skip '#', keep "Z3_..."
        let end = rest
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        let ident = &rest[..end];
        rest = &rest[end..];
        // Strip trailing () if present (function cross-reference style)
        rest = rest.strip_prefix("()").unwrap_or(rest);
        out.push_str(&format!("[`{ident}`]"));
    }
    out.push_str(rest);
    out
}

/// Replace single-line `\code content \endcode` with `` `content` ``.
/// Multi-line code blocks are handled by the state machine in process_doc_string.
fn replace_inline_code(s: &str) -> String {
    const OPEN: &str = r"\code ";
    const CLOSE: &str = r" \endcode";
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(start) = rest.find(OPEN) {
        out.push_str(&rest[..start]);
        let after_open = &rest[start + OPEN.len()..];
        if let Some(end) = after_open.find(CLOSE) {
            let content = after_open[..end].trim();
            out.push('`');
            out.push_str(content);
            out.push('`');
            rest = &after_open[end + CLOSE.len()..];
        } else {
            // No closing tag on this line — leave as-is.
            out.push_str(OPEN);
            rest = after_open;
        }
    }
    out.push_str(rest);
    out
}

/// Apply all inline Doxygen-to-Markdown transforms to a line.
fn apply_inline(s: &str) -> String {
    let s = replace_inline_code(s);
    let s = replace_ccode(&s);
    let s = replace_c_ref(&s);
    replace_hash_ref(&s)
}

/// Parsing state for multi-line block commands.
#[derive(PartialEq)]
enum DocBlock {
    Normal,
    Code,     // inside \code ... \endcode  → fenced ```c
    Verbatim, // inside \verbatim ... \endverbatim → fenced ```
}

/// Convert a raw Doxygen doc string (from `#[doc = "..."]`) to Rust markdown.
fn process_doc_string(raw: &str) -> String {
    // Doxygen sometimes wraps `\c word` across a line break in C headers
    // (e.g. "the result is \c\nZ3_L_TRUE"). Join so replace_c_ref can match.
    // In the string value, `\c` is the two bytes '\' and 'c'; `\n` is newline.
    let joined;
    let raw = if raw.contains("\\c\n") {
        joined = raw.replace("\\c\n", "\\c ");
        &joined
    } else {
        raw
    };

    let mut out: Vec<String> = Vec::new();
    let mut preconditions: Vec<String> = Vec::new();
    let mut see_also: Vec<String> = Vec::new();
    let mut first = true;
    let mut block = DocBlock::Normal;

    for line in raw.lines() {
        // Inside a code or verbatim block — pass lines through until the closer.
        if block != DocBlock::Normal {
            let t = line.trim();
            let end_tag = if block == DocBlock::Code { r"\endcode" } else { r"\endverbatim" };
            if t == end_tag {
                out.push("```".to_string());
                block = DocBlock::Normal;
            } else {
                out.push(line.to_string());
            }
            continue;
        }

        if is_strip_line(line) {
            continue;
        }

        if let Some(names) = extract_sa(line) {
            see_also.extend(names);
            continue;
        }

        // Strip \brief prefix wherever it appears.
        // Bindgen can merge adjacent doc comments (e.g. "Similar to X.\n\brief Y."),
        // so we strip it on any line, not just the first.
        let line = {
            let t = line.trim_start();
            if first {
                first = false;
                if t == r"\brief" {
                    continue; // bare \brief — description starts on the next line
                }
                t.strip_prefix(r"\brief ").unwrap_or(t)
            } else if let Some(rest) = t.strip_prefix(r"\brief ") {
                rest
            } else if t == r"\brief" {
                continue;
            } else {
                line
            }
        };

        let t = line.trim_start();

        // Multi-line code block opener.
        if t == r"\code" {
            out.push("```c".to_string());
            block = DocBlock::Code;
            continue;
        }
        if t == r"\verbatim" {
            out.push("```".to_string());
            block = DocBlock::Verbatim;
            continue;
        }

        // Block-level Doxygen commands.
        if let Some(rest) = t.strip_prefix(r"\remark ").or_else(|| {
            if t == r"\remark" { Some("") } else { None }
        }) {
            out.push(format!("**Remark:** {}", apply_inline(rest.trim_end())));
            continue;
        }

        if let Some(rest) = t.strip_prefix(r"\note ").or_else(|| {
            if t == r"\note" { Some("") } else { None }
        }) {
            out.push(format!("**Note:** {}", apply_inline(rest.trim_end())));
            continue;
        }

        if let Some(rest) = t.strip_prefix(r"\pre ") {
            preconditions.push(apply_inline(rest.trim_end()));
            continue;
        }

        if let Some(rest) = t.strip_prefix(r"\param ") {
            let rest = rest.trim();
            if let Some((name, desc)) = rest.split_once(|c: char| c.is_whitespace()) {
                out.push(format!("- `{}`: {}", name, apply_inline(desc.trim_start())));
            } else {
                out.push(format!("- `{rest}`"));
            }
            continue;
        }

        // Regular line — apply inline transforms.
        out.push(apply_inline(line));
    }

    // Trim trailing blank lines.
    while out.last().is_some_and(|l| l.is_empty()) {
        out.pop();
    }

    if !preconditions.is_empty() {
        out.push(String::new());
        out.push("# Preconditions".to_string());
        out.push(String::new());
        for pre in preconditions {
            out.push(format!("- `{pre}`"));
        }
    }

    if !see_also.is_empty() {
        out.push(String::new());
        out.push("# See also".to_string());
        out.push(String::new());
        for sa in see_also {
            out.push(format!("- [`{sa}`]"));
        }
    }

    out.join("\n")
}

/// Extract the string value from a `#[doc = "..."]` attribute, if it is one.
fn doc_string(attr: &Attribute) -> Option<String> {
    if !attr.path().is_ident("doc") {
        return None;
    }
    if let Meta::NameValue(MetaNameValue { value: Expr::Lit(ExprLit { lit: Lit::Str(s), .. }), .. }) =
        &attr.meta
    {
        Some(s.value())
    } else {
        None
    }
}

/// Build per-line `#[doc = " line"]` attributes from a processed string.
fn doc_attrs(processed: &str) -> Vec<Attribute> {
    processed
        .lines()
        .map(|line| {
            let content = format!(" {line}");
            syn::parse_quote!(#[doc = #content])
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Function transformation
// ---------------------------------------------------------------------------

fn transform_fn(mut func: ForeignItemFn) -> ForeignItemFn {
    // Wrap opaque-handle return types in Option<>.
    func.sig.output = match func.sig.output {
        ReturnType::Default => ReturnType::Default,
        ReturnType::Type(arrow, ty) if is_opaque_handle(&ty) => {
            let wrapped: Type = syn::parse_quote!(Option<#ty>);
            ReturnType::Type(arrow, Box::new(wrapped))
        }
        ret => ret,
    };

    // Process doc attributes.
    let mut new_attrs: Vec<Attribute> = Vec::new();
    for attr in func.attrs {
        if let Some(raw) = doc_string(&attr) {
            let processed = process_doc_string(&raw);
            if !processed.is_empty() {
                new_attrs.extend(doc_attrs(&processed));
            }
        } else {
            new_attrs.push(attr);
        }
    }
    func.attrs = new_attrs;

    func
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("failed to read bindgen output from stdin");

    let file: syn::File = syn::parse_str(&input).expect("failed to parse bindgen output as Rust");

    let functions: Vec<ForeignItemFn> = file
        .items
        .into_iter()
        .filter_map(|item| match item {
            Item::ForeignMod(foreign_mod) => Some(foreign_mod.items),
            _ => None,
        })
        .flatten()
        .filter_map(|foreign_item| match foreign_item {
            ForeignItem::Fn(func) => Some(transform_fn(func)),
            _ => None,
        })
        .collect();

    let output = quote! {
        unsafe extern "C" {
            #(#functions)*
        }
    };

    let output_file: syn::File = syn::parse2(output).expect("failed to parse transformed output");
    let header = "// Auto-generated by scripts/gen-bindings.sh — do not edit manually.\n\
                  // Run `scripts/gen-bindings.sh` to regenerate.\n\
                  // Run `scripts/check-bindings.sh` to verify coverage against z3-sys/src/lib.rs.\n\n";
    print!("{}{}", header, prettyplease::unparse(&output_file));
}
