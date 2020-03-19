fn main() {
    #[cfg(feature = "static-link-z3")]
    build_z3();
}

#[cfg(feature = "static-link-z3")]
fn build_z3() {
    let dst = cmake::Config::new("z3")
        // Don't build `libz3.so`, build `libz3.a` instead.
        .define("Z3_BUILD_LIBZ3_SHARED", "false")
        // Don't build the Z3 repl.
        .define("Z3_BUILD_EXECUTABLE", "false")
        // Don't build the tests.
        .define("Z3_BUILD_TEST_EXECUTABLES", "false")
        .build();

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

    if let Some(cxx) = cxx {
        println!("cargo:rustc-link-lib={}", cxx);
    }

    println!(
        "cargo:rustc-link-search=native={}",
        dst.join("lib").display()
    );
    println!("cargo:rustc-link-lib=static=z3");
}
