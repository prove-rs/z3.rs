# `z3` and `z3-sys`

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

Starting with version 0.20.0, z3-rs aims to track the latest Z3 release and stay up-to-date with API changes.

| z3      | z3-sys   | upstream Z3      |
|---------|----------|------------------|
| ≤0.19.x | ≤0.10.x  | 4.8.12 – 4.16.0  |
| ≥0.20.0 | ≥0.11.0  | ≥4.16.0          |

### ≤0.19.x (z3-sys ≤0.10.x): broad version support

Function and opaque structure FFI bindings were generated and committed sometime around Z3 4.8.12 
and updated ad-hoc, but enum bindings were re-generated via bindgen on every build. 
This let the enums track whatever Z3 version was linked, giving broad 4.8.12–4.16.0 support. The cost was
that new high-level Z3 APIs could not easily be defined without feature-gating, and were often
omitted entirely.

### ≥0.20.0 (z3-sys ≥0.11.0): static generated bindings

Both functions and enums are tracked in version control
(`z3-sys/src/generated/functions.rs` and `z3-sys/src/generated/enums.rs`). There is by default no
dynamic bindgen step on every build. The minimum supported upstream Z3 version is 4.16.0.

FFI bindings can be regenerated for new Z3 versions by running
`cargo xtask gen-bindings`.

Users who wish to generate FFI bindings at build-time for their system's Z3 can build with
the `bindgen` feature enabled; note though that while the low-level bindings may work,
the high-level bindings will not be able to link against (old) versions of z3 that do not
export the necessary symbols.

## When should I use `z3-sys` instead of `z3`?

The first scenario where it makes sense to use `z3-sys` directly is when some Z3
feature isn't wrapped into high-level bindings in the `z3` crate yet. In this
case, it is worth filing an issue and discussing its implementation in the `z3`
crate, but you can get at the raw, underlying features via the `z3-sys` crate in
the meantime.

The only other time to use `z3-sys` directly would be if you are writing your
own custom high-level API for Z3, instead of using the `z3` crate.
