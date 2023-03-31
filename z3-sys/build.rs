#[cfg(not(feature = "dynamic-link-z3"))]
#[cfg(not(feature = "static-link-z3"))]
const Z3_RELEASE: &str = "z3-4.12.1";

#[cfg(target_os = "windows")]
const ARCHIVE_FILENAME: &str = "z3-4.12.1-x64-win.zip";
#[cfg(target_os = "linux")]
const ARCHIVE_FILENAME: &str = "z3-4.12.1-x64-glibc-2.35.zip";
#[cfg(target_os = "macos")]
const ARCHIVE_FILENAME: &str = "z3-4.12.1-x64-osx-10.16.zip";

fn main() {
    get_z3();
}

#[cfg(not(feature = "dynamic-link-z3"))]
#[cfg(not(feature = "static-link-z3"))]
/// Use precompiled Z3 binaries.
fn get_z3() {
    let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let archive_url = format!("https://github.com/Z3Prover/z3/releases/download/{}/{}", Z3_RELEASE, ARCHIVE_FILENAME);
    let archive_path = out_dir.join(ARCHIVE_FILENAME);

    // Download
    {
        let f = std::fs::File::create(&archive_path).unwrap();
        let mut writer = std::io::BufWriter::new(f);
        let response = ureq::get(&archive_url).call().unwrap();
        assert_eq!(response.status(), 200);
        let mut reader = response.into_reader();
        std::io::copy(&mut reader, &mut writer).unwrap();
    }

    // Extract
    let file = std::fs::File::open(&archive_path).unwrap();
    let mut archive = zip::ZipArchive::new(file).unwrap();
    archive.extract(&out_dir).unwrap();
    let lib_dir = out_dir.join(archive_path.file_stem().unwrap());

    // Add lib folder to the library search path.
    println!("cargo:rustc-link-search=native={}", lib_dir.join("bin").to_str().unwrap());
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

    let mut found_lib_dir = None;
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
            found_lib_dir = Some(full_lib_dir);
            break;
        }
    }

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
