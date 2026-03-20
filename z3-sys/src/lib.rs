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
//! | `vendored` | Build Z3 from source using `cmake` and statically link it |
//! | `bundled` | **Deprecated.** Alias for `vendored`; will be removed in a future release |
//! | `gh-release` | Build against a pre-compiled Z3 static library from GitHub Releases |
//! | `vcpkg` | Use a Z3 installed via vcpkg |
//! | `bindgen` | Regenerate `functions.rs` from local Z3 headers at build time |
//!
//! ## Environment variables
//!
//! ### `vendored` feature
//!
//! The `vendored` feature builds Z3 from source using `cmake` and statically
//! links it. The Z3 source tree is shipped inside the [`z3-src`] crate and
//! compiled locally — no network access is required at build time.
//!
//! By default the Z3 version built is whatever version `z3-src` bundles. To use
//! a specific version without managing source yourself, `gh-release` with
//! `Z3_SYS_Z3_VERSION` is a simpler alternative.
//!
//! **Using your own Z3 checkout:** Set `Z3_SRC_SOURCE_DIR` to the **absolute
//! path** of a Z3 source tree:
//!
//! ```text
//! Z3_SRC_SOURCE_DIR=/absolute/path/to/z3 cargo build
//! ```
//!
//! To use a **project-relative** path, add the following to your project's
//! `.cargo/config.toml`. The `relative = true` key tells Cargo to resolve
//! the path relative to the config file's location:
//!
//! ```toml
//! [env]
//! Z3_SRC_SOURCE_DIR = { value = "path/to/z3", relative = true }
//! ```
//!
//! > **Note:** A `z3` directory in your own project or workspace is **not**
//! > picked up automatically — you must set `Z3_SRC_SOURCE_DIR` explicitly,
//! > even if you have a Z3 git submodule in your repo.
//!
//! [`z3-src`]: https://crates.io/crates/z3-src
//!
//! ### Other variables
//!
//! | Variable | Feature | Description |
//! |----------|---------|-------------|
//! | `Z3_SYS_Z3_HEADER` | `bindgen` | Path to `z3.h`; defaults to `z3-src/z3/src/api/z3.h` |
//! | `Z3_SYS_UPDATE_GENERATED` | `bindgen` | Set to `1` to also write `src/generated/functions.rs` and `src/generated/enums.rs` |
//! | `Z3_LIBRARY_PATH_OVERRIDE` | default | Add an extra library search path for the linker |
//! | `Z3_SYS_Z3_VERSION` | `gh-release` | Z3 version to download (e.g. `4.13.0`) |
//! | `READ_ONLY_GITHUB_TOKEN` | `gh-release` | GitHub PAT to avoid API rate limits in CI |
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

mod types;

pub use types::*;

#[cfg(not(feature = "bindgen"))]
include!("generated/functions.rs");

#[cfg(not(feature = "bindgen"))]
include!("generated/enums.rs");

#[cfg(feature = "bindgen")]
include!(concat!(env!("OUT_DIR"), "/functions.rs"));

#[cfg(feature = "bindgen")]
include!(concat!(env!("OUT_DIR"), "/enums.rs"));

include!("functions_patched.rs");

#[cfg(not(windows))]
#[link(name = "z3")]
unsafe extern "C" {}

#[cfg(windows)]
#[link(name = "libz3")]
unsafe extern "C" {}
