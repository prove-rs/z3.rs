use std::{env, path::PathBuf};

fn main() {
    let args: Vec<String> = env::args().collect();
    assert_eq!(args.len(), 2);
    bindgen(PathBuf::from(&args[1]))
}

fn bindgen(z3_header: PathBuf) {
    let header = z3_header.display().to_string();
    #[cfg(target_os = "linux")]
    let out_path = PathBuf::new().join("z3-sys").join("src").join("generated_linux");
    #[cfg(target_os = "windows")]
    let out_path = PathBuf::new().join("z3-sys").join("src").join("generated_windows");
    #[cfg(target_os = "macos")]
    let out_path = PathBuf::new().join("z3-sys").join("src").join("generated_macos");

    for x in &[
        "ast_kind",
        "ast_print_mode",
        "decl_kind",
        "error_code",
        "goal_prec",
        "param_kind",
        "parameter_kind",
        "sort_kind",
        "symbol_kind",
    ] {
        let enum_bindings = bindgen::Builder::default()
            .header(&header)
            .parse_callbacks(Box::new(bindgen::CargoCallbacks))
            .generate_comments(false)
            .rustified_enum(format!("Z3_{}", x))
            .allowlist_type(format!("Z3_{}", x));

        enum_bindings
            .generate()
            .expect("Unable to generate bindings")
            .write_to_file(out_path.join(format!("{}.rs", x)))
            .expect("Couldn't write bindings!");
    }
}
