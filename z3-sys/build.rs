#[cfg(feature = "use-bindgen")]
const Z3_HEADER_VAR: &str = "Z3_SYS_Z3_HEADER";

#[cfg(not(feature = "dynamic-link-z3"))]
#[cfg(not(feature = "static-link-z3"))]
const Z3_RELEASE: &str = "z3-4.8.12";

#[cfg(target_os = "windows")]
const Z3_ARCH: &str = "x64-win";
#[cfg(target_os = "linux")]
const Z3_ARCH: &str = "x64-glibc-2.31";

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    get_z3();
    #[cfg(feature = "use-bindgen")]
    bindgen();
}

#[cfg(not(feature = "dynamic-link-z3"))]
#[cfg(not(feature = "static-link-z3"))]
/// Use precompiled Z3 binaries.
fn get_z3() {
    let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let archive_filename = format!("{}-{}", Z3_RELEASE, Z3_ARCH);
    let archive_url = format!("https://github.com/Z3Prover/z3/releases/download/{}/{}.zip", Z3_RELEASE, archive_filename);
    let archive_path = out_dir.join(format!("{}.zip", archive_filename));
    let release_folder = out_dir.join(archive_filename);

    let curl = std::process::Command::new("curl")
        .arg("-L")
        .arg("-o")
        .arg(&archive_path.to_str().unwrap())
        .arg(&archive_url)
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    assert!(curl.success());

    #[cfg(target_os = "windows")]
    let tar = std::process::Command::new("tar")
        .current_dir(archive_path.parent().unwrap())
        .arg("-x")
        .arg("-f")
        .arg(&archive_path.to_str().unwrap())
        .spawn()
        .unwrap()
        .wait()
        .unwrap();

    #[cfg(not(target_os = "windows"))]
    let tar = std::process::Command::new("unzip")
        .current_dir(archive_path.parent().unwrap())
        .arg(&archive_path.to_str().unwrap())
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    assert!(tar.success());

    // Add lib folder to the library search path.
    println!("cargo:rustc-link-search=native={}/bin", &release_folder.to_str().unwrap());
}

#[cfg(feature = "dynamic-link-z3")]
#[cfg(not(feature = "static-link-z3"))]
/// Use the system's Z3 installation.
fn get_z3() {}

#[cfg(not(feature = "dynamic-link-z3"))]
#[cfg(feature = "static-link-z3")]
#[cfg(not(target_os = "windows"))]
/// Build and link Z3 statically on Linux/MacOS
fn get_z3() {
    let mut cfg = cmake::Config::new("z3");
    cfg
        // Don't build `libz3.so`, build `libz3.a` instead.
        .define("Z3_BUILD_LIBZ3_SHARED", "false")
        // Don't build the Z3 repl.
        .define("Z3_BUILD_EXECUTABLE", "false")
        // Don't build the tests.
        .define("Z3_BUILD_TEST_EXECUTABLES", "false");

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
            } else if target.contains("apple") {
                Some("c++".to_string())
            } else if target.contains("freebsd") {
                Some("c++".to_string())
            } else if target.contains("openbsd") {
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

    if let Some(cxx) = cxx {
        println!("cargo:rustc-link-lib={}", cxx);
    }
}

#[cfg(not(feature = "dynamic-link-z3"))]
#[cfg(feature = "static-link-z3")]
#[cfg(target_os = "windows")]
/// Build and link Z3 statically on Windows
fn get_z3() {
    let mut cfg = cmake::Config::new("z3");
    cfg
        // Don't build `libz3.so`, build `libz3.a` instead.
        .define("Z3_BUILD_LIBZ3_SHARED", "false")
        // Don't build the Z3 repl.
        .define("Z3_BUILD_EXECUTABLE", "false")
        // Don't build the tests.
        .define("Z3_BUILD_TEST_EXECUTABLES", "false");
        // The compiler option -MP and the msbuild option -m
        // can sometimes make builds slower but is measurably
        // faster building Z3 with many cores.
        cfg.cxxflag("-MP");
        cfg.build_arg("-m");
        cfg.cxxflag("-DWIN32");
        cfg.cxxflag("-D_WINDOWS");

    let dst = cfg.build();

    // Add lib folder to the library search path.
    println!("cargo:rustc-link-search=native={}/lib", dst.to_str().unwrap());
}

#[cfg(feature = "use-bindgen")]
fn bindgen() {
    let header = if cfg!(feature = "static-link-z3") {
        "z3/src/api/z3.h".to_string()
    } else if let Ok(header_path) = std::env::var(Z3_HEADER_VAR) {
        header_path
    } else {
        "wrapper.h".to_string()
    };
    println!("cargo:rerun-if-env-changed={}", Z3_HEADER_VAR);
    println!("cargo:rerun-if-changed={}", header);
    let out_path = std::path::PathBuf::from("generated".unwrap());

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
            .allowlist_type(format!("Z3_{}", x))
            .generate()
            .expect("Unable to generate bindings");

        if env::var("TARGET").unwrap() == "wasm32-unknown-emscripten" {
            enum_bindings = enum_bindings.clang_arg(format!(
                "--sysroot={}/upstream/emscripten/cache/sysroot",
                env::var("EMSDK").expect("$EMSDK env var missing. Is emscripten installed?")
            ));
        }

        enum_bindings
            .write_to_file(out_path.join(format!("{}.rs", x)))
            .expect("Couldn't write bindings!");
    }
}
