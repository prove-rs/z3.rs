use std::env;

const Z3_HEADER_VAR: &str = "Z3_SYS_Z3_HEADER";

fn main() {
    #[cfg(feature = "static-link-z3")]
    let include_dir = prepare_z3();

    println!("cargo:rerun-if-changed=build.rs");

    let header = if let Ok(header_path) = std::env::var(Z3_HEADER_VAR) {
        header_path
    } else {
        "wrapper.h".to_string()
    };
    println!("cargo:rerun-if-env-changed={}", Z3_HEADER_VAR);
    println!("cargo:rerun-if-changed={}", header);
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
            .header(&header)
            .parse_callbacks(Box::new(bindgen::CargoCallbacks))
            .generate_comments(false)
            .rustified_enum(format!("Z3_{}", x))
            .allowlist_type(format!("Z3_{}", x));

        #[cfg(feature = "static-link-z3")]
        {
            enum_bindings = enum_bindings.clang_arg(&format!("-I{}", &include_dir));
        }

        if env::var("TARGET").unwrap() == "wasm32-unknown-emscripten" {
            enum_bindings = enum_bindings.clang_arg(format!(
                "--sysroot={}/upstream/emscripten/cache/sysroot",
                env::var("EMSDK").expect("$EMSDK env var missing. Is emscripten installed?")
            ));
        }
        enum_bindings
            .generate()
            .expect("Unable to generate bindings")
            .write_to_file(out_path.join(format!("{}.rs", x)))
            .expect("Couldn't write bindings!");
    }
}

#[cfg(feature = "static-link-z3")]
fn prepare_z3() -> String {
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
    println!("cargo:rerun-if-env-changed=CXXSTDLIB");

    if let Some(cxx) = cxx {
        println!("cargo:rustc-link-lib={}", cxx);

        // The following linker flags are needed for `cargo test` to compile
        // test binaries.
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        {
            let cxx_paths = [
                "/usr/lib/gcc/x86_64-linux-gnu/13",
                "/usr/lib/gcc/x86_64-linux-gnu/12",
                "/usr/lib/gcc/x86_64-linux-gnu/11",
                "/usr/lib/gcc/x86_64-linux-gnu/10",
                "/usr/lib/gcc/x86_64-linux-gnu/9",
                "/usr/lib/gcc/x86_64-linux-gnu/8",
                "/usr/lib/gcc/x86_64-linux-gnu/7",
                "/usr/lib/x86_64-linux-gnu",
                "/usr/lib64",
                "/usr/lib",
            ];

            for path in cxx_paths {
                if std::fs::read_dir(std::path::PathBuf::from(path)).is_ok() {
                    println!("cargo:rustc-link-arg=-Lnative={}", path);
                }
            }
            println!("cargo:rustc-link-arg=-l{}", cxx);
        }
    }

    if cfg!(target_os = "windows") {
        println!("cargo:rustc-link-lib=static=libz3");
    } else {
        println!("cargo:rustc-link-lib=static=z3");
    }
    #[cfg(not(feature = "force-build-z3"))]
    if let Some(ret) = download_z3() {
        return ret;
    }
    build_z3()
}

#[cfg(feature = "static-link-z3")]
fn build_z3() -> String {
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

    "z3/src/api".to_string()
}

#[cfg(feature = "static-link-z3")]
#[cfg(not(feature = "force-build-z3"))]
fn download_z3() -> Option<String> {
    use reqwest::blocking;
    use sha2::{Digest, Sha256};
    use std::ffi::OsStr;
    use std::fs::File;
    use std::io::{Cursor, Read, Write};
    use std::path::{Path, PathBuf};
    use zip::ZipArchive;
    fn download(url: &str, sha256: &str) -> Result<Vec<u8>, String> {
        let buf = (|| -> reqwest::Result<_> {
            let response = blocking::get(url)?.error_for_status()?;
            Ok(response.bytes()?.iter().cloned().collect::<Vec<_>>())
        })()
        .map_err(|e| e.to_string())?;
        if sha256 != "PASS" {
            let hash = Sha256::digest(&buf);
            if format!("{:x}", hash) != sha256 {
                return Err("Hash check failed".to_string());
            }
        }
        Ok(buf)
    }

    fn get_archive_url() -> Option<(String, String)> {
        if cfg!(target_os = "linux") && cfg!(target_arch = "x86_64") {
            Some((
                "https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-glibc-2.35.zip".into(),
                "c5360fd157b0f861ec8780ba3e51e2197e9486798dc93cd878df69a4b0c2b7c5".into(),
            ))
        } else if cfg!(target_os = "macos") && cfg!(target_arch = "x86_64") {
            Some((
                "https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-osx-10.16.zip".into(),
                "7601f844de6d906235140d0f76cca58be7ac716f3e2c29c35845aa24b24f73b9".into(),
            ))
        } else if cfg!(target_os = "macos") && cfg!(target_arch = "aarch64") {
            Some((
                "https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-arm64-osx-11.0.zip".into(),
                "91664cb7c10279e533f7ec568d63e0d04ada352217a6710655d41739c4ea1fc8".into(),
            ))
        } else if cfg!(target_os = "windows")
            && cfg!(target_arch = "x86_64")
            && cfg!(target_env = "msvc")
        {
            Some((
                "https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-win.zip"
                    .into(),
                "ce2d658d007c4f5873d2279bd031d4e72500b388e1ef2d716bd5f86af19b20d2".into(),
            ))
        } else if cfg!(target_os = "windows")
            && cfg!(target_arch = "x86")
            && cfg!(target_env = "msvc")
        {
            Some((
                "https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x86-win.zip"
                    .into(),
                "1fbe8e2a87f42ca6f3348b8c48a1ffcd8fc376ac3144c9b588a5452de01ca2ef".into(),
            ))
        } else {
            None
        }
    }

    fn find_origin_dir_and_get_successor_path(path: &Path, name: &OsStr) -> Option<PathBuf> {
        let segs = path.parent()?.iter().collect::<Vec<_>>();
        segs.iter()
            .enumerate()
            .find(|seg| *seg.1 == name)
            .map(|(i, _)| {
                segs[segs.len() - i + 1..]
                    .iter()
                    .fold(PathBuf::new(), |path, seg| path.join(seg))
            })
    }

    fn write_lib_to_dir(out_dir: &Path) -> Option<()> {
        let (url, hash) = get_archive_url()?;
        let archive = download(&url, &hash).unwrap();
        let mut archive = ZipArchive::new(Cursor::new(archive)).unwrap();
        for i in 0..archive.len() {
            let mut file = archive.by_index(i).unwrap();
            let path = PathBuf::from(file.name());
            let out_dir = if let Some(succ) =
                find_origin_dir_and_get_successor_path(&path, OsStr::new("bin"))
            {
                Some(out_dir.to_path_buf().join(Path::new("lib")).join(succ))
            } else {
                find_origin_dir_and_get_successor_path(&path, OsStr::new("include"))
                    .map(|succ| out_dir.to_path_buf().join(Path::new("include")).join(succ))
            };

            if let Some(mut out_dir) = out_dir {
                let mut buf = Vec::with_capacity(file.size() as usize);
                file.read_to_end(&mut buf).unwrap();
                std::fs::create_dir_all(&out_dir).unwrap();
                out_dir.push(path.file_name().unwrap());
                let mut outfile = File::create(&out_dir).unwrap();
                outfile.write_all(&buf).unwrap();
            }
        }
        Some(())
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    write_lib_to_dir(&out_dir)?;
    println!(
        "cargo:rustc-link-search=native={}",
        out_dir.clone().join(PathBuf::from("lib")).to_str().unwrap()
    );

    Some(
        std::fs::canonicalize(out_dir.clone().join(PathBuf::from("include")))
            .unwrap()
            .to_str()
            .unwrap()
            .to_string(),
    )
}
