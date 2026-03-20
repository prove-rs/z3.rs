use std::{
    env,
    path::{Path, PathBuf},
};

const Z3_SRC_SOURCE_DIR: &str = "Z3_SRC_SOURCE_DIR";

/// Build artifacts produced by compiling Z3 from source.
pub struct Artifacts {
    include_dir: PathBuf,
    lib_dir: PathBuf,
}

impl Artifacts {
    /// Path to the directory containing `z3.h`.
    pub fn include_dir(&self) -> &Path {
        &self.include_dir
    }

    /// Path to the directory containing the static Z3 library.
    pub fn lib_dir(&self) -> &Path {
        &self.lib_dir
    }

    /// Emit `cargo:rustc-link-*` directives. Call this from your `build.rs`.
    pub fn print_cargo_metadata(&self) {
        println!("cargo:rustc-link-search=native={}", self.lib_dir.display());
        // Windows uses "libz3", Unix uses "z3"
        if cfg!(target_os = "windows") {
            println!("cargo:rustc-link-lib=static=libz3");
        } else {
            println!("cargo:rustc-link-lib=static=z3");
        }
    }
}

/// Build Z3 from source and return the resulting artifacts.
///
/// Call this from your crate's `build.rs`.
///
/// Source resolution priority:
/// 1. `Z3_SRC_SOURCE_DIR` environment variable
/// 2. Bundled source at `$CARGO_MANIFEST_DIR/z3/` (the submodule)
/// 3. Panics with a clear message
pub fn build() -> Artifacts {
    println!("cargo:rerun-if-env-changed={Z3_SRC_SOURCE_DIR}");

    let src_dir = resolve_source();

    let dst = build_cmake(&src_dir);

    let lib_dir = find_lib_dir(&dst);

    let include_dir = dst.join("include");

    Artifacts {
        include_dir,
        lib_dir,
    }
}

fn resolve_source() -> PathBuf {
    if let Ok(dir) = env::var(Z3_SRC_SOURCE_DIR) {
        let path = PathBuf::from(dir);
        assert!(
            path.exists(),
            "{Z3_SRC_SOURCE_DIR} points to non-existent path: {}",
            path.display()
        );
        return path;
    }

    // env!() bakes in z3-src's own manifest directory at z3-src compile time,
    // so this works correctly even when called from another crate's build.rs.
    let submodule = Path::new(env!("CARGO_MANIFEST_DIR")).join("z3");
    if submodule.exists() {
        return submodule;
    }

    // Note that this panic should only be reachable in dev contexts: the crate has the
    // source tree from the submodule prepublished already, so the above "submodule" check
    // should always work.
    //
    // If, however, someone is developing on this library and has it checked out through git,
    // and did not check out submodules, this may be hit, hence the message.
    panic!("Z3 source not found — run `git submodule update --init` or set {Z3_SRC_SOURCE_DIR}");
}

fn build_cmake(src_dir: &Path) -> PathBuf {
    let mut cfg = cmake::Config::new(src_dir);

    cfg.define("Z3_BUILD_LIBZ3_SHARED", "false")
        .define("Z3_BUILD_EXECUTABLE", "false")
        .define("Z3_BUILD_TEST_EXECUTABLES", "false")
        .define("Z3_ENABLE_EXAMPLE_TARGETS", "false");

    if cfg!(target_os = "windows") {
        // -MP and -m enable parallel compilation, measurably faster for Z3.
        cfg.cxxflag("-MP");
        cfg.build_arg("-m");
        cfg.cxxflag("-DWIN32");
        cfg.cxxflag("-D_WINDOWS");
        cfg.define("CMAKE_MSVC_RUNTIME_LIBRARY", "MultiThreadedDLL");
    } else if env::var("TARGET").unwrap().starts_with("wasm") {
        // Z3 uses exceptions, which must be explicitly enabled for WASM.
        cfg.no_default_flags(true).cxxflag("-fexceptions");
    }

    cfg.build()
}

fn find_lib_dir(dst: &Path) -> PathBuf {
    for candidate in &["lib", "lib64"] {
        let dir = dst.join(candidate);
        if dir.exists() {
            if *candidate == "lib64" {
                assert_eq!(
                    env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap(),
                    "64",
                    "lib64 only valid for 64-bit targets"
                );
            }
            return dir;
        }
    }
    panic!(
        "Could not find lib directory in Z3 build output at {}",
        dst.display()
    );
}
