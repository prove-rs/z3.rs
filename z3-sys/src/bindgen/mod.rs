mod bindgen_transform;

pub fn generate_bindings() -> bindgen_transform::TransformOutput {
    use std::path::PathBuf;

    let header = if let Ok(h) = std::env::var("Z3_SYS_Z3_HEADER") {
        PathBuf::from(h)
    } else {
        #[cfg(feature = "vendored")]
        {
            z3_src::build().include_dir().join("z3.h")
        }
        #[cfg(not(feature = "vendored"))]
        panic!(
            "Set Z3_SYS_Z3_HEADER to the path of z3.h, \
             or enable the `vendored` feature to use the vendored Z3 source"
        )
    };
    let include_dir = header.parent().unwrap();

    println!("cargo:rerun-if-env-changed=Z3_SYS_Z3_HEADER");
    println!("cargo:rerun-if-env-changed=Z3_SYS_UPDATE_GENERATED");

    // Generate function declarations (types blocklisted — hand-written in types.rs).
    // Functions with nullable parameters that require Option<T> signatures are blocklisted
    // here and hand-written in src/functions_patched.rs instead.
    let funcs_raw = bindgen::Builder::default()
        .use_core()
        .disable_header_comment()
        .allowlist_function("Z3_.*")
        .blocklist_type("Z3_.*")
        .blocklist_type("_Z3_.*")
        .blocklist_function("Z3_mk_constructor")
        .blocklist_function("Z3_fixedpoint_add_rule")
        .blocklist_function("Z3_optimize_assert_soft")
        .header(header.to_str().unwrap())
        .clang_arg(format!("-I{}", include_dir.display()))
        .generate()
        .expect("bindgen failed (functions)")
        .to_string();

    // Generate enum type definitions (rustified, one invocation for all enums).
    let enums_raw = bindgen::Builder::default()
        .use_core()
        .disable_header_comment()
        .allowlist_type("Z3_sort_kind")
        .allowlist_type("Z3_ast_kind")
        .allowlist_type("Z3_decl_kind")
        .allowlist_type("Z3_symbol_kind")
        .allowlist_type("Z3_goal_prec")
        .allowlist_type("Z3_parameter_kind")
        .allowlist_type("Z3_param_kind")
        .allowlist_type("Z3_ast_print_mode")
        .allowlist_type("Z3_error_code")
        .rustified_enum("Z3_.*")
        .header(header.to_str().unwrap())
        .clang_arg(format!("-I{}", include_dir.display()))
        .generate()
        .expect("bindgen failed (enums)")
        .to_string();

    // Combine and transform.  transform() dispatches Item::Enum and Item::ForeignMod.
    let combined = format!("{funcs_raw}\n{enums_raw}");
    bindgen_transform::transform(&combined)
}
