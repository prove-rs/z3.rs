use std::env;

const Z3_HEADER_VAR: &str = "Z3_SYS_Z3_HEADER";

#[cfg(not(feature = "vcpkg"))]
fn main() {
    #[cfg(feature = "static-link-z3")]
    build_z3();

    println!("cargo:rerun-if-changed=build.rs");

    let header = if cfg!(feature = "static-link-z3") {
        "z3/src/api/z3.h".to_string()
    } else if let Ok(header_path) = std::env::var(Z3_HEADER_VAR) {
        header_path
    } else {
        "wrapper.h".to_string()
    };
    println!("cargo:rerun-if-env-changed={}", Z3_HEADER_VAR);
    println!("cargo:rerun-if-changed={}", header);

    generate_binding(&header);
}

#[cfg(feature = "vcpkg")]
fn main() {
    let lib = vcpkg::Config::new()
        .emit_includes(true)
        .find_package("z3")
        .unwrap();
    let found_header = lib.include_paths.iter().any(|include| {
        let mut include = include.clone();
        include.push("z3.h");
        if include.exists() {
            generate_binding(include.to_str().unwrap());
            true
        } else {
            false
        }
    });
    assert!(
        found_header,
        "z3.h is not found in include path of installed z3."
    );
}

fn generate_binding(header: &str) {
    let out_path = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());

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
            .parse_callbacks(Box::new(bindgen::CargoCallbacks))
            .generate_comments(false)
            .rustified_enum(format!("Z3_{}", x))
            .allowlist_type(format!("Z3_{}", x));
        let target = env::var("TARGET").unwrap();
        let wasm32 = target.starts_with("wasm32-unknown");
        let wasm32_emscripten = target == "wasm32-unknown-emscripten";
        if wasm32 {
            let sysroot = env::var("EMSDK")
                .map(|emsdk| format!("{}/upstream/emscripten/cache/sysroot", emsdk))
                .or_else(|_err| {
                    env::var("EMSCRIPTEN_ROOT")
                        .map(|emscripten_root| format!("{}/cache/sysroot", emscripten_root))
                });
            if let Ok(sysroot) = sysroot {
                enum_bindings = enum_bindings.clang_arg(format!("--sysroot={}", sysroot));
            } else if wasm32_emscripten {
                panic!("$EMSDK and $EMSCRIPTEN_ROOT env var missing. Is emscripten installed?");
            }
        }
        enum_bindings
            .generate()
            .expect("Unable to generate bindings")
            .write_to_file(out_path.join(format!("{}.rs", x)))
            .expect("Couldn't write bindings!");
    }
}

#[cfg(feature = "static-link-z3")]
fn build_z3() {
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

    // Z3 needs a C++ standard library. Customize which one we use with the
    // `CXXSTDLIB` environment variable, if needed.
    let cxx = match std::env::var("CXXSTDLIB") {
        Ok(s) if s.is_empty() => None,
        Ok(s) => Some(s),
        Err(_) => {
            let target = std::env::var("TARGET").unwrap();
            if target.contains("msvc") {
                None
            } else if target.contains("apple")
                | target.contains("freebsd")
                | target.contains("openbsd")
            {
                Some("c++".to_string())
            } else {
                Some("stdc++".to_string())
            }
        }
    };

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
                assert_eq!(
                    std::env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap(),
                    "64"
                );
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

    if let Some(cxx) = cxx {
        println!("cargo:rustc-link-lib={}", cxx);
    }
}
