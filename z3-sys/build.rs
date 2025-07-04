use std::{env, path::PathBuf};

macro_rules! assert_one_of_features {
    ($($feature:literal),*) => {
        let mut active_count = 0;
        $(
            if cfg!(feature = $feature) {
                active_count += 1;
            }
        )*
        if active_count > 1 {
            panic!("Only one of the features [{}] can be active at a time", stringify!($($feature),*));
        }
    };
}

fn main() {
    // Check that only one of the mutually exclusive features is active
    assert_one_of_features!("bundled", "vcpkg", "gh-release");

    // Don't need to specify this for these build configurations.
    #[cfg(any(feature = "bundled", feature = "vcpkg", feature = "gh-release"))]
    let search_paths = vec![];

    #[cfg(feature = "bundled")]
    build_bundled_z3();

    #[cfg(feature = "gh-release")]
    let header = install_from_gh_release();

    #[cfg(not(any(feature = "bundled", feature = "vcpkg", feature = "gh-release")))]
    let search_paths = {
        if let Ok(lib) = pkg_config::Config::new().probe("z3") {
            lib.include_paths
        } else {
            vec![]
        }
    };

    #[cfg(feature = "deprecated-static-link-z3")]
    println!("cargo:warning=The 'static-link-z3' feature is deprecated. Please use the 'bundled' feature.");

    println!("cargo:rerun-if-changed=build.rs");

    #[cfg(not(any(feature = "vcpkg", feature = "gh-release")))]
    let header = find_header_by_env();

    #[cfg(feature = "vcpkg")]
    let header = find_library_header_by_vcpkg();

    link_against_cxx_stdlib();

    generate_binding(&header, &search_paths);
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

#[cfg(feature = "gh-release")]
mod gh_release {
    use reqwest::blocking::{Client, ClientBuilder};

    use super::*;

    pub(super) fn install_from_gh_release() -> String {
        let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();
        let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
        let (header, lib) = retrieve_gh_release_z3(&target_os, &target_arch);
        println!(
            "cargo:rustc-link-search=native={}",
            lib.parent().unwrap().display()
        );
        if cfg!(target_os = "windows") {
            println!("cargo:rustc-link-lib=static=libz3");
        } else {
            println!("cargo:rustc-link-lib=static=z3");
        }
        header.to_string_lossy().to_string()
    }

    fn retrieve_gh_release_z3(target_os: &str, target_arch: &str) -> (PathBuf, PathBuf) {
        let arch = match target_arch {
            "aarch64" => "arm64",
            "x86_64" => "x64",
            arch => {
                panic!("Unsupported architecture: {}", arch);
            }
        };
        let os = match target_os {
            "windows" => "win",
            "linux" => "glibc",
            "macos" => "osx",
            os => {
                panic!("Unsupported OS: {}", os);
            }
        };
        println!("cargo:rerun-if-env-changed=Z3_SYS_Z3_VERSION");
        let z3_version = env::var("Z3_SYS_Z3_VERSION").unwrap_or("4.15.2".to_string());

        let client = ClientBuilder::new().user_agent("z3-sys").build().unwrap();

        let url = get_release_asset_url(&client, &z3_version, &os, &arch);
        let Some(z3_dir) = download_unzip(&client, url) else {
            panic!(
                "Could not get release asset for z3-{} with os={} and arch={}",
                z3_version, os, arch
            );
        };

        let header = z3_dir.join("include/z3.h");
        let lib = if cfg!(target_os = "windows") {
            z3_dir.join("bin/libz3.lib")
        } else {
            z3_dir.join("bin/libz3.a")
        };

        assert!(
            header.exists(),
            "could not find z3.h in downloaded archive at {}",
            z3_dir.display()
        );
        assert!(
            lib.exists(),
            "could not find static libz3 in downloaded archive at {}",
            z3_dir.display()
        );

        (header, lib)
    }

    fn download_unzip(client: &Client, url: String) -> Option<PathBuf> {
        let response = client.get(url).send().ok()?;
        assert_eq!(response.status(), 200);
        let ziplib = response.bytes().ok()?;

        println!("Downloaded {}MB", ziplib.len() as f64 / 1024.0 / 1024.0);

        let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
        let z3_dir = out_dir.join("z3");
        zip_extract::extract(std::io::Cursor::new(ziplib), &z3_dir, true).unwrap();

        Some(z3_dir)
    }

    fn get_release_asset_url(
        client: &Client,
        z3_version: &str,
        target_os: &str,
        target_arch: &str,
    ) -> String {
        let release_url =
            format!("https://api.github.com/repos/Z3Prover/z3/releases/tags/z3-{z3_version}");
        let Ok(response) = client.get(release_url).send() else {
            panic!("Could not find release for z3-{}", z3_version);
        };

        assert_eq!(response.status(), 200);

        let release_json: serde_json::Value =
            serde_json::from_str(&response.text().unwrap()).unwrap();

        let assets = release_json.get("assets").unwrap().as_array().unwrap();

        let Some(asset) = assets.iter().find(|a| {
            let name = a.get("name").unwrap().as_str().unwrap();
            name.contains(target_os)
                && name.contains(target_arch)
                && name.ends_with(".zip")
                && name.starts_with("z3-")
        }) else {
            panic!(
                "Could not find asset for z3-{} with os={} and arch={}",
                z3_version, target_os, target_arch
            );
        };

        asset
            .get("browser_download_url")
            .unwrap()
            .as_str()
            .unwrap()
            .to_owned()
    }
}
#[cfg(feature = "gh-release")]
use gh_release::install_from_gh_release;

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

#[cfg(not(any(feature = "vcpkg", feature = "gh-release")))]
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

fn generate_binding(header: &str, search_paths: &[PathBuf]) {
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());

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
        #[allow(unused_mut)]
        let mut enum_bindings = bindgen::Builder::default()
            .header(header)
            .generate_comments(false)
            .rustified_enum(format!("Z3_{x}"))
            .allowlist_type(format!("Z3_{x}"))
            .clang_args(search_paths.iter().map(|p| format!("-I{}", p.display())));
        // Deactivate bindgen cargo-rerun-if generation for gh-release (unnecessary)
        #[cfg(not(feature = "gh-release"))]
        let mut enum_bindings =
            enum_bindings.parse_callbacks(Box::new(bindgen::CargoCallbacks::new()));
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
        cfg.define("CMAKE_MSVC_RUNTIME_LIBRARY", "MultiThreadedDLL");
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
