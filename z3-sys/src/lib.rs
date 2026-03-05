//! # Z3
//!
//! Z3 is a theorem prover [from Microsoft Research](https://github.com/Z3Prover/z3/).
//!
//! This crate provides low-level bindings that provide no real
//! affordances for usage from Rust and that mirror the C API.
//!
//! For bindings that are easier to use from Rust, see the higher level
//! bindings in the [Z3](https://crates.io/crates/z3/) crate.
//!
//! # Build configuration
//!
//! This crate needs to locate a Z3 library at build time. The method is
//! controlled by Cargo features and environment variables.
//!
//! ## Features
//!
//! | Feature | Behaviour |
//! |---------|-----------|
//! | *(default)* | Link against a system-installed Z3 (`brew install z3`, etc.) |
//! | `bundled` | Build Z3 from source using `cmake` and statically link it |
//! | `gh-release` | Build against a pre-compiled Z3 static library from GitHub Releases |
//! | `vcpkg` | Use a Z3 installed via vcpkg |
//! | `bindgen` | Regenerate `functions.rs` from local Z3 headers at build time |
//!
//! ## Environment variables
//!
//! ### `bundled` feature
//!
//! The `bundled` feature builds Z3 from source using `cmake` and statically
//! links it. Despite the name, **Z3 source is not included in the crate
//! tarball** published to crates.io. In cases where the user does not provide
//! the source tree, the z3-sys `build.rs` script _must reach out to GitHub
//! to fetch the source tree_. At build time, the build script resolves
//! a Z3 source tree in the following order:
//!
//! 1. **`Z3_SYS_BUNDLED_DIR_OVERRIDE` is set** — that path is used directly;
//!    no network access occurs.
//! 2. **Build output cache** (`OUT_DIR/z3`) already exists from a prior
//!    build — the cached source is reused; no network access occurs.
//! 3. **Local submodule** (`CARGO_MANIFEST_DIR/z3`) exists — only relevant
//!    when building `z3-sys` itself from its git repository, not when using
//!    it as a crate dependency.
//! 4. **GitHub fetch** — the build script calls the GitHub Contents API to
//!    look up which Z3 commit the `z3-sys` git submodule pointed to at the
//!    time of the current release (using the `z3-sys-vX.Y.Z` git tag), then
//!    downloads and extracts that Z3 source archive into `OUT_DIR/z3`.
//!
//! By default, the Z3 version built is whatever commit the `z3-sys` release
//! pinned in its submodule. You can build any (compatible) Z3 version by pointing
//! `Z3_SYS_BUNDLED_DIR_OVERRIDE` at your own checkout (see below). To use a
//! specific version without managing source yourself, `gh-release` with
//! `Z3_SYS_Z3_VERSION` is a simpler alternative.
//!
//! > **Network access:** A first build from crates.io requires outbound HTTPS
//! > to `api.github.com` (submodule ref lookup) and `github.com` (archive
//! > download). Set `READ_ONLY_GITHUB_TOKEN` to a GitHub PAT to avoid
//! > rate-limiting in CI. The downloaded source is cached in `OUT_DIR` and
//! > reused on subsequent builds until `cargo clean`.
//!
//! **Using your own Z3 checkout:** Set `Z3_SYS_BUNDLED_DIR_OVERRIDE` to the
//! **absolute path** of a Z3 source tree to skip the network fetch entirely:
//!
//! ```text
//! Z3_SYS_BUNDLED_DIR_OVERRIDE=/absolute/path/to/z3 cargo build
//! ```
//!
//! To use a **project-relative** path, add the following to your project's
//! `.cargo/config.toml`. The `relative = true` key tells Cargo to resolve
//! the path relative to the config file's location:
//!
//! ```toml
//! [env]
//! Z3_SYS_BUNDLED_DIR_OVERRIDE = { value = "path/to/z3", relative = true }
//! ```
//!
//! > **Note:** A `z3` directory in your own project or workspace is **not**
//! > picked up automatically — you must set `Z3_SYS_BUNDLED_DIR_OVERRIDE`
//! > explicitly, even if you have a Z3 git submodule in your repo.
//!
//! ### Other variables
//!
//! | Variable | Feature | Description |
//! |----------|---------|-------------|
//! | `Z3_SYS_Z3_HEADER` | `bindgen` | Path to `z3.h`; defaults to `z3-src/z3/src/api/z3.h` |
//! | `Z3_SYS_UPDATE_GENERATED` | `bindgen` | Set to `1` to also write `src/generated/functions.rs` and `src/generated/enums.rs` |
//! | `Z3_LIBRARY_PATH_OVERRIDE` | default | Add an extra library search path for the linker |
//! | `Z3_SYS_Z3_VERSION` | `gh-release` | Z3 version to download (e.g. `4.13.0`) |
//! | `READ_ONLY_GITHUB_TOKEN` | `bundled`, `gh-release` | GitHub PAT to avoid API rate limits in CI |
//! | `CXXSTDLIB` | any | Override which C++ standard library to link (e.g. `c++`, `stdc++`) |
//!
//! # Example
//!
//! ```
//! use z3_sys::*;
//!
//! unsafe {
//!     let cfg = Z3_mk_config().unwrap();
//!     let ctx = Z3_mk_context(cfg).unwrap();
//!
//!     let a = Z3_mk_not(ctx, Z3_mk_eq(ctx, Z3_mk_false(ctx).unwrap(), Z3_mk_true(ctx).unwrap()).unwrap()).unwrap();
//!     let b = Z3_mk_not(ctx, Z3_mk_iff(ctx, Z3_mk_false(ctx).unwrap(), Z3_mk_true(ctx).unwrap()).unwrap()).unwrap();
//!     assert_eq!(Z3_mk_true(ctx), Z3_simplify(ctx, a));
//!     assert_eq!(Z3_mk_true(ctx), Z3_simplify(ctx, b));
//!
//!     Z3_del_config(cfg);
//!     Z3_del_context(ctx);
//! }
//! ```

#![allow(non_camel_case_types)]
#![allow(clippy::unreadable_literal)]
// Generated C API docs don't conform to Rust doc formatting conventions.
#![allow(clippy::doc_markdown)]
#![allow(clippy::doc_lazy_continuation)]
#![no_std]

mod generated;
mod types;

pub use generated::*;
pub use types::*;

#[cfg(not(feature = "bindgen"))]
include!("generated/functions.rs");

#[cfg(feature = "bindgen")]
include!(concat!(env!("OUT_DIR"), "/functions.rs"));

include!("functions_patched.rs");

#[cfg(not(windows))]
#[link(name = "z3")]
unsafe extern "C" {}

#[cfg(windows)]
#[link(name = "libz3")]
unsafe extern "C" {}
