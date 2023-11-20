use std::env;

fn main() {
    #[cfg(feature = "bundled")]
    build_bundled_z3();

    #[cfg(feature = "deprecated-static-link-z3")]
    println!("cargo:warning=The 'static-link-z3' feature is deprecated. Please use the 'bundled' feature.");

    println!("cargo:rerun-if-changed=build.rs");

    #[cfg(not(feature = "vcpkg"))]
    let header = find_header_by_env();

    #[cfg(feature = "vcpkg")]
    let header = find_library_header_by_vcpkg();

    link_against_cxx_stdlib();

    generate_binding(&header);
}

fn link_against_cxx_stdlib() {
    // Z3 needs a C++ standard library. Customize which one we use with the
    // `CXXSTDLIB` environment variable, if needed.
    let cxx = match env::var("CXXSTDLIB") {
        Ok(s) if s.is_empty() => None,
        Ok(s) => Some(s),
        Err(_) => {
            let target = env::var("TARGET").unwrap();
            if target.contains("msvc") {
                None
            } else if target.contains("apple")
                | target.contains("freebsd")
                | target.contains("openbsd")
            {
                Some("c++".to_string())
            } else if target.contains("android") {
                Some("c++_shared".to_string())
            } else {
                Some("stdc++".to_string())
            }
        }
    };

    println!("cargo:rerun-if-env-changed=CXXSTDLIB");
    if let Some(cxx) = cxx {
        println!("cargo:rustc-link-lib={cxx}");
    }
}

#[cfg(feature = "vcpkg")]
fn find_library_header_by_vcpkg() -> String {
    let lib = vcpkg::Config::new()
        .emit_includes(true)
        .find_package("z3")
        .unwrap();
    for include in &lib.include_paths {
        let mut include = include.clone();
        include.push("z3.h");
        if include.exists() {
            let header = include.to_str().unwrap().to_owned();
            println!("cargo:rerun-if-changed={header}");
            return header;
        }
    }
    panic!("z3.h is not found in include path of installed z3.");
}

#[cfg(not(feature = "vcpkg"))]
fn find_header_by_env() -> String {
    const Z3_HEADER_VAR: &str = "Z3_SYS_Z3_HEADER";
    let header = if cfg!(feature = "bundled") {
        "z3/src/api/z3.h".to_string()
    } else if let Ok(header_path) = env::var(Z3_HEADER_VAR) {
        header_path
    } else {
        "wrapper.h".to_string()
    };
    println!("cargo:rerun-if-env-changed={Z3_HEADER_VAR}");
    println!("cargo:rerun-if-changed={header}");
    header
}

fn generate_binding(header: &str) {
    let out_path = std::path::PathBuf::from(env::var("OUT_DIR").unwrap());

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
        let mut enum_bindings = bindgen::Builder::default()
            .header(header)
            .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
            .generate_comments(false)
            .rustified_enum(format!("Z3_{x}"))
            .allowlist_type(format!("Z3_{x}"));
        if env::var("TARGET").unwrap() == "wasm32-unknown-emscripten" {
            enum_bindings = enum_bindings.clang_arg(format!(
                "--sysroot={}/upstream/emscripten/cache/sysroot",
                env::var("EMSDK").expect("$EMSDK env var missing. Is emscripten installed?")
            ));
        }
        enum_bindings
            .generate()
            .expect("Unable to generate bindings")
            .write_to_file(out_path.join(format!("{x}.rs")))
            .expect("Couldn't write bindings!");
    }
}

/// Build z3 with bundled source codes.
#[cfg(feature = "bundled")]
fn build_bundled_z3() {
    let mut cfg = cmake::Config::new("z3");
    cfg
        // Don't build `libz3.so`, build `libz3.a` instead.
        .define("Z3_BUILD_LIBZ3_SHARED", "false")
        // Don't build the Z3 repl.
        .define("Z3_BUILD_EXECUTABLE", "false")
        // Don't build the tests.
        .define("Z3_BUILD_TEST_EXECUTABLES", "false");

    if cfg!(target_os = "windows") {
        // The compiler option -MP and the msbuild option -m
        // can sometimes make builds slower but is measurably
        // faster building Z3 with many cores.
        cfg.cxxflag("-MP");
        cfg.build_arg("-m");
        cfg.cxxflag("-DWIN32");
        cfg.cxxflag("-D_WINDOWS");
    }

    let dst = cfg.build();

    let mut found_lib_dir = false;
    for lib_dir in &[
        "lib",
        // Fedora builds seem to use `lib64` rather than `lib` for 64-bit
        // builds.
        "lib64",
    ] {
        let full_lib_dir = dst.join(lib_dir);
        if full_lib_dir.exists() {
            if *lib_dir == "lib64" {
                assert_eq!(env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap(), "64");
            }
            println!("cargo:rustc-link-search=native={}", full_lib_dir.display());
            found_lib_dir = true;
            break;
        }
    }
    assert!(
        found_lib_dir,
        "Should have found the lib directory for our built Z3"
    );

    if cfg!(target_os = "windows") {
        println!("cargo:rustc-link-lib=static=libz3");
    } else {
        println!("cargo:rustc-link-lib=static=z3");
    }
}
