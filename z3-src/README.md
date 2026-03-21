# z3-src

Source distribution of the [Z3 SMT solver](https://github.com/Z3Prover/z3), modeled after
[`openssl-src`](https://crates.io/crates/openssl-src). Intended for use as a build dependency
when you want to compile Z3 from source rather than link against a system-installed copy.

Most users do not depend on `z3-src` directly — it is pulled in automatically when you enable the
`vendored` feature on [`z3-sys`](https://crates.io/crates/z3-sys) or
[`z3`](https://crates.io/crates/z3) (the `bundled` feature is a deprecated alias for `vendored`).

## Versioning

The crate version encodes the bundled Z3 release:

```
{Z3_major}{Z3_minor:02}.{Z3_patch}.{packaging_revision}
```

For example, `416.0.0` bundles Z3 4.16.0.

## Usage as a direct build dependency

If you maintain your own Z3 FFI bindings and want to compile Z3 from source, add `z3-src` as a
build dependency:

```toml
[build-dependencies]
z3-src = "416"
```

Then call `z3_src::build()` from your `build.rs`:

```rust
fn main() {
    let artifacts = z3_src::build();
    artifacts.print_cargo_metadata();
    // artifacts.include_dir() — path containing z3.h
    // artifacts.lib_dir()     — path containing the static library
}
```

`print_cargo_metadata()` emits the `cargo:rustc-link-search` and `cargo:rustc-link-lib` directives
needed to link against the compiled static library.

## Environment variables

| Variable | Description |
|----------|-------------|
| `Z3_SRC_SOURCE_DIR` | Override the Z3 source directory. Useful for pointing at a local Z3 checkout instead of the bundled copy. |

## Prerequisites

- **CMake** — must be on `PATH` at build time.
- **C++ compiler** — a compiler supported by Z3's CMake build (GCC, Clang, MSVC).

Build times are significant (~5 minutes on a modern machine). Incremental rebuilds are cached by
Cargo in `OUT_DIR`.

## Platform notes

| Platform | Notes |
|----------|-------|
| Linux / macOS | Links `libz3.a` + `libstdc++` or `libc++` as appropriate. |
| Windows (MSVC) | Links `libz3.lib`. Parallel compilation (`/MP`) is enabled automatically. |
| WASM | C++ exception support (`-fexceptions`) is enabled automatically. |

The C++ standard library used for linking can be overridden with the `CXXSTDLIB` environment
variable (set to an empty string to skip linking a C++ stdlib entirely).

## License

`z3-src` is MIT-licensed. Z3 itself is also
[MIT-licensed](https://github.com/Z3Prover/z3/blob/master/LICENSE.txt).
