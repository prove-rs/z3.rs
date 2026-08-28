use std::env;
#[cfg(feature = "gh-release")]
use std::path::PathBuf;

#[cfg(not(feature = "bindgen"))]
mod enum_compat;
mod version;

#[cfg(feature = "gh-release")]
const GH_RELEASE_VERSION: &str = "5.1.0";

macro_rules! assert_one_of_features {
    ($($feature:literal),*) => {{
        let mut active_count = 0;
        let mut active_feature = None;
        $(
            if cfg!(feature = $feature) {
                active_count += 1;
                active_feature = Some($feature);
            }
        )*
        if active_count > 1 {
            panic!("Only one of the features [{}] can be active at a time", stringify!($($feature),*));
        }
        active_feature
    }};
}

fn main() {
    // Check that only one of the mutually exclusive features is active
    let active_feature = assert_one_of_features!("vendored", "vcpkg", "gh-release");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=Z3_SYS_Z3_VERSION");
    let override_version = env::var("Z3_SYS_Z3_VERSION")
        .ok()
        .and_then(|s| version::parse_dotted(&s));

    let detected_version = match active_feature {
        Some("vendored") => build_from_source(),
        Some("gh-release") => install_from_gh_release(),
        Some("vcpkg") => find_library_by_vcpkg(),
        _ => {
            let detected = pkg_config::Config::new()
                .probe("z3")
                .ok()
                .and_then(|lib| detect_pkg_config_version(&lib))
                .or_else(detect_cli_version);
            println!("cargo:rerun-if-env-changed=Z3_LIBRARY_PATH_OVERRIDE");
            if let Ok(lib_path) = env::var("Z3_LIBRARY_PATH_OVERRIDE") {
                println!("cargo:rustc-link-search=native={lib_path}");
            }
            detected
        }
    };

    emit_version_metadata(override_version.or(detected_version));

    #[cfg(feature = "bundled")]
    println!(
        "cargo:warning=The 'bundled' feature is deprecated. Please use the 'vendored' feature."
    );

    link_against_cxx_stdlib();

    #[cfg(feature = "bindgen")]
    generate_bindings();
}

/// Emits the detected Z3 version (or the assumed minimum, if detection
/// failed) as `links`-passthrough metadata for downstream crates (see
/// `DEP_Z3_VERSION_*` / `DEP_Z3_MIN_SUPPORTED_*` in `z3/build.rs`), and warns
/// if it's below the minimum supported version.
fn emit_version_metadata(version: Option<version::Version>) {
    let min = version::MIN_SUPPORTED;
    let version = match version {
        Some(v) if v < min => {
            println!(
                "cargo:warning=z3-sys: detected Z3 {v}, but z3-sys requires Z3 >= {min}. \
                 Upgrade your Z3 installation, or if this detection is wrong, override with \
                 Z3_SYS_Z3_VERSION=<version> (must still satisfy the minimum). Proceeding with \
                 the detected version; the build may fail or behave incorrectly."
            );
            v
        }
        Some(v) => v,
        None => {
            println!(
                "cargo:warning=z3-sys: could not detect linked Z3 version; assuming minimum \
                 supported {min}. Newer version-gated APIs will be unavailable. Set \
                 Z3_SYS_Z3_VERSION to override."
            );
            min
        }
    };

    println!("cargo:version_major={}", version.major);
    println!("cargo:version_minor={}", version.minor);
    println!("cargo:version_patch={}", version.patch);
    println!("cargo:min_supported_major={}", min.major);
    println!("cargo:min_supported_minor={}", min.minor);
    println!("cargo:min_supported_patch={}", min.patch);

    // With `bindgen`, enums are regenerated fresh from the actual linked header on every
    // build, so the static compatibility table doesn't apply.
    #[cfg(not(feature = "bindgen"))]
    enum_compat::warn_on_mismatches(version);
}

fn detect_pkg_config_version(lib: &pkg_config::Library) -> Option<version::Version> {
    version::parse_dotted(&lib.version).or_else(|| {
        lib.include_paths
            .iter()
            .find_map(|dir| version::parse_header(&dir.join("z3_version.h")))
    })
}

/// Falls back to shelling out to the `z3` CLI binary for version detection
/// when no pkg-config metadata is available (e.g. Z3 installed from a
/// prebuilt release archive, which ships no `.pc` file).
fn detect_cli_version() -> Option<version::Version> {
    let output = std::process::Command::new("z3")
        .arg("--version")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    version::parse_cli_output(&String::from_utf8_lossy(&output.stdout))
}

#[cfg(feature = "vendored")]
fn build_from_source() -> Option<version::Version> {
    let artifacts = z3_src::build();
    artifacts.print_cargo_metadata();
    version::parse_header(&artifacts.include_dir().join("z3_version.h"))
}

#[cfg(not(feature = "vendored"))]
fn build_from_source() -> Option<version::Version> {
    unreachable!()
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
    use std::path::Path;
    use std::time::Duration;

    use super::*;
    use reqwest::blocking::{Client, ClientBuilder};
    use reqwest::header::{AUTHORIZATION, HeaderMap};
    use zip::ZipArchive;
    use zip::read::root_dir_common_filter;

    pub(super) fn install_from_gh_release() -> Option<crate::version::Version> {
        let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();
        let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
        let (lib, version) = retrieve_gh_release_z3(&target_os, &target_arch);
        println!(
            "cargo:rustc-link-search=native={}",
            lib.parent().unwrap().display()
        );
        if cfg!(target_os = "windows") {
            println!("cargo:rustc-link-lib=static=libz3");
        } else {
            println!("cargo:rustc-link-lib=static=z3");
        }
        version
    }

    fn retrieve_gh_release_z3(
        target_os: &str,
        target_arch: &str,
    ) -> (PathBuf, Option<crate::version::Version>) {
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
        let z3_version = env::var("Z3_SYS_Z3_VERSION").unwrap_or(GH_RELEASE_VERSION.to_string());
        let version = crate::version::parse_dotted(&z3_version);
        let z3_dir = PathBuf::from(env::var("OUT_DIR").unwrap()).join(format!("z3-{z3_version}"));

        if !z3_dir.exists() {
            let client = get_github_client();

            let url = get_release_asset_url(&client, &z3_version, os, arch);
            if let Err(err) = download_unzip(&client, url, &z3_dir) {
                println!("error: {err}");
                panic!(
                    "Could not get release asset for z3-{} with os={} and arch={}",
                    z3_version, os, arch
                );
            };
        } else {
            println!("Found cached z3 at {}", z3_dir.display());
        }

        let lib = if cfg!(target_os = "windows") {
            z3_dir.join("bin/libz3.lib")
        } else {
            z3_dir.join("bin/libz3.a")
        };

        assert!(
            lib.exists(),
            "could not find static libz3 in downloaded archive at {}",
            z3_dir.display()
        );

        (lib, version)
    }

    pub fn download_unzip(client: &Client, url: String, dir: &Path) -> reqwest::Result<()> {
        let response = client.get(url).send()?;
        assert_eq!(response.status(), 200);
        let ziplib = response.bytes()?;

        println!("Downloaded {:0.2}MB", ziplib.len() as f64 / 1024.0 / 1024.0);

        ZipArchive::new(std::io::Cursor::new(ziplib))
            .unwrap()
            .extract_unwrapped_root_dir(dir, root_dir_common_filter)
            .expect("Failed to extract z3 release asset");
        Ok(())
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

    pub fn get_github_client() -> Client {
        let client = ClientBuilder::new()
            .user_agent("z3-sys")
            .timeout(Duration::from_secs(300));
        let mut headers = HeaderMap::new();
        if let Ok(val) = env::var("READ_ONLY_GITHUB_TOKEN") {
            headers.insert(AUTHORIZATION, format!("Bearer {val}").parse().unwrap());
        }
        client.default_headers(headers).build().unwrap()
    }
}
#[cfg(feature = "gh-release")]
use gh_release::install_from_gh_release;

#[cfg(not(feature = "gh-release"))]
fn install_from_gh_release() -> Option<version::Version> {
    unreachable!()
}

#[cfg(feature = "vcpkg")]
fn find_library_by_vcpkg() -> Option<version::Version> {
    let lib = vcpkg::Config::new()
        .emit_includes(true)
        .find_package("z3")
        .expect("vcpkg could not find z3");
    lib.include_paths
        .iter()
        .find_map(|dir| version::parse_header(&dir.join("z3_version.h")))
}

#[cfg(not(feature = "vcpkg"))]
fn find_library_by_vcpkg() -> Option<version::Version> {
    unreachable!()
}

#[cfg(feature = "bindgen")]
mod bindgen_transform;

#[cfg(feature = "bindgen")]
fn generate_bindings() {
    use std::fs;
    use std::path::PathBuf;

    let header = if let Ok(h) = env::var("Z3_SYS_Z3_HEADER") {
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
    let output = bindgen_transform::transform(&combined);

    let header_comment = "// Auto-generated by z3-sys bindgen feature — do not edit manually.\n\n";
    let funcs_src = format!("{header_comment}{}", output.functions);
    let enums_src = format!("{header_comment}{}", output.enums);

    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    fs::write(out.join("functions.rs"), &funcs_src).expect("write functions.rs to OUT_DIR");
    fs::write(out.join("enums.rs"), &enums_src).expect("write enums.rs to OUT_DIR");

    if env::var("Z3_SYS_UPDATE_GENERATED").is_ok() {
        let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        let r#gen = manifest.join("src/generated");

        let committed_funcs = r#gen.join("functions.rs");
        fs::write(&committed_funcs, &funcs_src).expect("write committed functions.rs");
        println!("cargo:warning=Updated {}", committed_funcs.display());

        let committed_enums = r#gen.join("enums.rs");
        fs::write(&committed_enums, &enums_src).expect("write committed enums.rs");
        println!("cargo:warning=Updated {}", committed_enums.display());
    }
}
