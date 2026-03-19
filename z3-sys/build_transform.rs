//! Transform raw bindgen output into z3-sys–compatible declarations.
//!
//! Reads bindgen-generated Rust source and writes transformed Rust to stdout.
//!
//! ## Function transformations
//!
//! Applied to each `extern "C"` function:
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
//!
//! ## Enum transformations
//!
//! Applied to each `pub enum Z3_xxx` definition:
//!
//! - Enum name: strip `Z3_` prefix, PascalCase the rest
//!   (`Z3_sort_kind` → `SortKind`, `Z3_decl_kind` → `DeclKind`)
//! - Variant names: strip `Z3_` prefix, strip common prefix/suffix component
//!   (e.g. `OP_` for `Z3_OP_*`, `_SORT` for `Z3_*_SORT`), then PascalCase
//! - `#[doc(alias = "Z3_original_name")]` added to enum and each variant
//! - Per-variant docs extracted from enum-level bullet-list (`- Z3_X desc`);
//!   variants not in the list fall back to "Corresponds to `Z3_X` in the C API."
//! - A `pub type Z3_original_name = NewName;` type alias is emitted after the enum

use std::collections::HashMap;

use quote::quote;
use syn::{
    Attribute, Expr, ExprLit, ForeignItem, ForeignItemFn, Item, ItemEnum, Lit, Meta, MetaNameValue,
    ReturnType, Type, Variant,
};

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
        .map(|s| s.trim_end_matches(['.', ',']).to_string())
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
    Nicebox,  // inside \nicebox{ ... }  → fenced ```
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
        // Inside a code, verbatim, or nicebox block — pass lines through until the closer.
        if block != DocBlock::Normal {
            let t = line.trim();
            let end_tag = match block {
                DocBlock::Code => r"\endcode",
                DocBlock::Verbatim => r"\endverbatim",
                DocBlock::Nicebox => "}",
                DocBlock::Normal => unreachable!(),
            };
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
        if t == r"\nicebox{" {
            out.push("```".to_string());
            block = DocBlock::Nicebox;
            continue;
        }

        // Block-level Doxygen commands.
        if let Some(rest) = t
            .strip_prefix(r"\remark ")
            .or_else(|| if t == r"\remark" { Some("") } else { None })
        {
            out.push(format!("**Remark:** {}", apply_inline(rest.trim_end())));
            continue;
        }

        if let Some(rest) = t
            .strip_prefix(r"\note ")
            .or_else(|| if t == r"\note" { Some("") } else { None })
        {
            out.push(format!("**Note:** {}", apply_inline(rest.trim_end())));
            continue;
        }

        if let Some(rest) = t
            .strip_prefix(r"\returns ")
            .or_else(|| if t == r"\returns" { Some("") } else { None })
        {
            out.push(format!("\n**Returns:** {}", apply_inline(rest.trim_end())));
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
    if let Meta::NameValue(MetaNameValue {
        value: Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        }),
        ..
    }) = &attr.meta
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
// Enum transformation helpers
// ---------------------------------------------------------------------------

/// Convert SCREAMING_SNAKE_CASE to PascalCase.
/// Each `_`-separated component has its first char uppercased, rest lowercased.
fn pascal_case(s: &str) -> String {
    s.split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                None => String::new(),
                Some(first) => {
                    let upper = first.to_uppercase().to_string();
                    let rest = chars.as_str().to_lowercase();
                    upper + &rest
                }
            }
        })
        .collect()
}

/// Describes what prefix or suffix to strip from a variant name.
#[derive(Debug)]
enum StripKind {
    Prefix(String), // e.g. "OP_" — strip from start
    Suffix(String), // e.g. "_SORT" — strip from end
    None,
}

/// Find a common prefix or suffix component (≥50% of variants) to strip.
///
/// Input: variant names AFTER stripping the leading `Z3_` prefix.
fn compute_strip_component(variants: &[&str]) -> StripKind {
    if variants.is_empty() {
        return StripKind::None;
    }
    let threshold = variants.len() / 2 + 1; // strictly more than half

    // Count frequency of each first component (part before first `_`).
    let mut prefix_counts: HashMap<&str, usize> = HashMap::new();
    for v in variants {
        let first = v.split('_').next().unwrap_or(v);
        *prefix_counts.entry(first).or_insert(0) += 1;
    }
    if let Some((best, &count)) = prefix_counts.iter().max_by_key(|&(_, &c)| c) {
        if count >= threshold {
            return StripKind::Prefix(format!("{best}_"));
        }
    }

    // Count frequency of each last component (part after last `_`).
    let mut suffix_counts: HashMap<&str, usize> = HashMap::new();
    for v in variants {
        if let Some(idx) = v.rfind('_') {
            let last = &v[idx + 1..];
            *suffix_counts.entry(last).or_insert(0) += 1;
        }
    }
    if let Some((best, &count)) = suffix_counts.iter().max_by_key(|&(_, &c)| c) {
        if count >= threshold {
            return StripKind::Suffix(format!("_{best}"));
        }
    }

    StripKind::None
}

/// Apply the strip component to a variant name (already has `Z3_` stripped).
fn apply_strip<'a>(variant: &'a str, strip: &StripKind) -> &'a str {
    match strip {
        StripKind::Prefix(p) => variant.strip_prefix(p.as_str()).unwrap_or(variant),
        StripKind::Suffix(s) => variant.strip_suffix(s.as_str()).unwrap_or(variant),
        StripKind::None => variant,
    }
}

/// Parse per-variant docs from an enum-level doc string.
///
/// Scans for bullet-list lines of the form `- Z3_VARIANT_NAME desc`, collecting
/// continuation lines (indented or blank) into the variant's doc.  Returns
/// `{ "Z3_VARIANT_NAME" => processed_doc }`.
fn parse_variant_docs(doc: &str) -> HashMap<String, String> {
    let mut map: HashMap<String, String> = HashMap::new();
    let mut current_name: Option<String> = None;
    let mut current_lines: Vec<&str> = Vec::new();

    // Inline flush: trim trailing blank lines, process, insert.
    macro_rules! flush {
        () => {
            if let Some(ref name) = current_name {
                let mut end = current_lines.len();
                while end > 0 && current_lines[end - 1].trim().is_empty() {
                    end -= 1;
                }
                let processed = process_doc_string(&current_lines[..end].join("\n"));
                if !processed.is_empty() {
                    map.insert(name.clone(), processed);
                }
            }
        };
    }

    for line in doc.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("- Z3_") {
            flush!();
            // Find end of the identifier portion: first char that isn't [A-Z0-9_].
            let name_end = rest
                .find(|c: char| !c.is_ascii_uppercase() && !c.is_ascii_digit() && c != '_')
                .unwrap_or(rest.len());
            if name_end == 0 {
                current_name = None;
                current_lines.clear();
                continue;
            }
            let variant_name = format!("Z3_{}", &rest[..name_end]);
            let after = rest[name_end..].trim_start_matches([' ', ':', '\t']);
            let first_text = after.strip_prefix("is ").unwrap_or(after).trim();
            current_name = Some(variant_name);
            current_lines.clear();
            if !first_text.is_empty() {
                current_lines.push(first_text);
            }
        } else if current_name.is_some() {
            // Any non-bullet line is a continuation of the current variant.
            // bindgen strips indentation, so we can't use starts_with(' ') to detect
            // continuations. Bullets always run to the next `- Z3_` or end of doc.
            current_lines.push(t);
        }
    }

    // Flush last variant.
    flush!();

    map
}

/// Return the enum-level doc with variant bullet-list lines removed.
///
/// Uses a state machine to drop entire bullet sections including
/// multi-line continuations and `\nicebox{...}` blocks.
fn strip_variant_bullets(doc: &str) -> String {
    let mut out: Vec<&str> = Vec::new();
    let mut in_bullet = false;

    for line in doc.lines() {
        let t = line.trim();
        if t.starts_with("- Z3_") {
            in_bullet = true;
            // skip bullet line
        } else if in_bullet {
            // Skip all continuation and blank lines.
            // bindgen strips indentation, so we can't rely on starts_with(' ') to
            // detect continuations. Bullet sections always extend to end of doc.
        } else {
            out.push(line);
        }
    }

    // Trim trailing blank lines.
    while out.last().is_some_and(|l| l.trim().is_empty()) {
        out.pop();
    }

    out.join("\n")
}

/// Transform a `Z3_xxx_kind` enum to an idiomatic Rust enum plus a type alias.
///
/// Returns `(renamed_enum, type_alias_item)`.
fn transform_enum(mut item: ItemEnum) -> (ItemEnum, proc_macro2::TokenStream) {
    let original_name = item.ident.to_string();

    // 1. Derive new enum name.
    let new_name_str = original_name
        .strip_prefix("Z3_")
        .map(pascal_case)
        .unwrap_or_else(|| original_name.clone());
    let new_ident: syn::Ident = syn::parse_str(&new_name_str).expect("valid enum ident");

    // 2. Collect enum-level doc and build variant-doc map.
    let raw_doc: String = item
        .attrs
        .iter()
        .filter_map(doc_string)
        .collect::<Vec<_>>()
        .join("\n");
    let variant_docs = parse_variant_docs(&raw_doc);
    let enum_doc_processed = process_doc_string(&strip_variant_bullets(&raw_doc));

    // 3. Compute strip component from variant names (after stripping Z3_ prefix).
    let variant_names_no_z3: Vec<String> = item
        .variants
        .iter()
        .map(|v| {
            let s = v.ident.to_string();
            s.strip_prefix("Z3_").unwrap_or(&s).to_string()
        })
        .collect();
    let variant_refs: Vec<&str> = variant_names_no_z3.iter().map(String::as_str).collect();
    let strip = compute_strip_component(&variant_refs);

    // 4. Transform each variant.
    let new_variants: Vec<Variant> = item
        .variants
        .iter()
        .cloned()
        .map(|mut variant| {
            let orig_name = variant.ident.to_string();
            let no_z3 = orig_name.strip_prefix("Z3_").unwrap_or(&orig_name);
            let stripped = apply_strip(no_z3, &strip);
            let new_variant_name = pascal_case(stripped);
            let new_variant_ident: syn::Ident =
                syn::parse_str(&new_variant_name).expect("valid variant ident");

            // Build variant doc: from bullet list or fallback.
            let variant_doc = variant_docs
                .get(&orig_name)
                .cloned()
                .unwrap_or_else(|| format!("Corresponds to `{orig_name}` in the C API."));

            // Build #[doc(alias = "ORIG_NAME")] attribute.
            let alias_attr: Attribute = syn::parse_quote!(#[doc(alias = #orig_name)]);

            let mut new_attrs = doc_attrs(&variant_doc);
            new_attrs.push(alias_attr);
            variant.attrs = new_attrs;
            variant.ident = new_variant_ident;
            variant
        })
        .collect();

    // 5. Build new enum attributes: doc + #[doc(alias)] + existing non-doc attrs.
    let orig_name_str = &original_name;
    let mut new_attrs: Vec<Attribute> = Vec::new();
    if !enum_doc_processed.is_empty() {
        new_attrs.extend(doc_attrs(&enum_doc_processed));
    }
    new_attrs.push(syn::parse_quote!(#[doc(alias = #orig_name_str)]));
    // Carry through non-doc attributes (e.g. #[repr(u32)], #[derive(...)]).
    for attr in &item.attrs {
        if doc_string(attr).is_none() {
            new_attrs.push(attr.clone());
        }
    }

    item.ident = new_ident.clone();
    item.attrs = new_attrs;
    item.variants = new_variants.into_iter().collect();

    // 6. Build type alias: `pub type Z3_original_name = NewName;`
    let orig_ident: syn::Ident = syn::parse_str(&original_name).expect("valid alias ident");
    let alias_tokens = quote! {
        pub type #orig_ident = #new_ident;
    };

    (item, alias_tokens)
}

// ---------------------------------------------------------------------------
// Output type
// ---------------------------------------------------------------------------

/// Output of [`transform`].
pub struct TransformOutput {
    /// Transformed `extern "C"` function declarations (content of `functions.rs`).
    pub functions: String,
    /// Transformed enum definitions and type aliases (content of `enums.rs`).
    pub enums: String,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Transform raw bindgen output into z3-sys–compatible declarations.
///
/// Parses the input as a Rust source file, then:
/// - Extracts all `ForeignItemFn` from any `extern "C"` blocks, applies
///   Doxygen-to-Markdown doc comment conversion and opaque-handle `Option<>`
///   wrapping, and returns them as a `prettyplease`-formatted `functions` string.
/// - Extracts all `enum` items, renames them from `Z3_xxx_kind` to `XxxKind`
///   style, PascalCases their variants, extracts per-variant docs from
///   enum-level bullet lists, and returns them plus type aliases as a
///   `prettyplease`-formatted `enums` string.
pub fn transform(input: &str) -> TransformOutput {
    let file: syn::File = syn::parse_str(input).expect("failed to parse bindgen output as Rust");

    let mut functions: Vec<ForeignItemFn> = Vec::new();
    let mut enum_items: Vec<proc_macro2::TokenStream> = Vec::new();

    for item in file.items {
        match item {
            Item::ForeignMod(foreign_mod) => {
                for foreign_item in foreign_mod.items {
                    if let ForeignItem::Fn(func) = foreign_item {
                        functions.push(transform_fn(func));
                    }
                }
            }
            Item::Enum(enum_item) => {
                let (transformed, alias) = transform_enum(enum_item);
                enum_items.push(quote! {
                    #transformed
                    #alias
                });
            }
            _ => {}
        }
    }

    // Format functions output.
    let funcs_tokens = quote! {
        unsafe extern "C" {
            #(#functions)*
        }
    };
    let funcs_file: syn::File =
        syn::parse2(funcs_tokens).expect("failed to parse transformed functions");
    let functions_str = prettyplease::unparse(&funcs_file);

    // Format enums output.
    let enums_tokens = quote! {
        #(#enum_items)*
    };
    let enums_file: syn::File =
        syn::parse2(enums_tokens).expect("failed to parse transformed enums");
    let enums_str = prettyplease::unparse(&enums_file);

    TransformOutput {
        functions: functions_str,
        enums: enums_str,
    }
}
