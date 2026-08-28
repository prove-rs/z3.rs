# `z3`, `z3-sys`, and `z3-src`

[![Rust](https://github.com/prove-rs/z3.rs/actions/workflows/rust.yml/badge.svg)](https://github.com/prove-rs/z3.rs/actions/workflows/rust.yml)

This repository contains [high-level][z3] and [low-level][z3-sys] Rust bindings
for the [Z3 solver][upstream].

[upstream]: https://github.com/Z3Prover/z3
[z3]: https://github.com/prove-rs/z3.rs/tree/master/z3
[z3-sys]: https://github.com/prove-rs/z3.rs/tree/master/z3-sys
[z3-src]: https://github.com/prove-rs/z3.rs/tree/master/z3-src

## `z3`

[![](https://img.shields.io/crates/v/z3.svg)](https://crates.io/crates/z3)

The [`z3` crate][z3] provides high-level bindings to the Z3 solver. It is built
on top of, and wraps, the `z3-sys` crate. This is the crate you'll want to use
99% of the time.

## `z3-sys`

[![](https://img.shields.io/crates/v/z3-sys.svg)](https://crates.io/crates/z3-sys)

The [`z3-sys` crate][z3-sys] provides the raw, unsafe, low-level C API that Z3
exposes.

## `z3-src`

[![](https://img.shields.io/crates/v/z3-src.svg)](https://crates.io/crates/z3-src)

The [`z3-src` crate][z3-src] contains the Z3 source distribution and logic to handle vendored builds.

## Z3 Version Compatibility

> [!IMPORTANT]
> Starting with version `0.21.0`, the `z3` and `z3-sys` crates have a minimum supported Z3 versions of 4.13.3.

Z3 incompatibility has two causes:

* Z3 sometimes adds APIs, making new C FFI targets, and causing linker errors if naively attempting to link against a too-new symbol in an old Z3 version.
* Z3 sometimes shuffles existing enum values while adding new ones.

The first issue means that using some z3 features imposes a minimum supported version. The second issue means that
`z3-sys` has a separate range of compatibility based on enum changes, independent of what high-level Z3 versions are used.

Starting with version `0.21.0`, this crate attempts to auto-detect the linked Z3 version and automatically enables all compatible features (without requiring user-enabled features). If
this version detection fails, it assumes the minimum supported version (4.13.3) and warns.

> [!TIP]
> The `z3-sys` crate will display a warning if you attempt to link against an incompatible Z3 version. Use `--features bindgen` or update Z3 to fix this.
> ```
> ~/R/z3.rs ❯❯❯ Z3_SYS_Z3_VERSION=4.16.0 cargo test --features gh-release
>    Compiling z3-sys v0.13.0 (/repos/z3.rs/z3-sys)
> warning: z3-sys@0.13.0: z3-sys: attempting to link against Z3 4.16.0 with `z3-sys` bindings for Z3 >= 5.0.0; enum numbering (e.g. Z3_decl_kind) may differ across these versions. Consider updating Z3 or else enabling the `bindgen` feature to ensure compatibility.
> ```

## When should I use `z3-sys` instead of `z3`?

The first scenario where it makes sense to use `z3-sys` directly is when some Z3
feature isn't wrapped into high-level bindings in the `z3` crate yet. In this
case, it is worth filing an issue and discussing its implementation in the `z3`
crate, but you can get at the raw, underlying features via the `z3-sys` crate in
the meantime.

The only other time to use `z3-sys` directly would be if you are writing your
own custom high-level API for Z3, instead of using the `z3` crate.
