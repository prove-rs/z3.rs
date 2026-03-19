# `z3` and `z3-sys`

[![Rust](https://github.com/prove-rs/z3.rs/actions/workflows/rust.yml/badge.svg)](https://github.com/prove-rs/z3.rs/actions/workflows/rust.yml)

This repository contains [high-level][z3] and [low-level][z3-sys] Rust bindings
for the [Z3 solver][upstream].

[upstream]: https://github.com/Z3Prover/z3
[z3]: https://github.com/prove-rs/z3.rs/tree/master/z3
[z3-sys]: https://github.com/prove-rs/z3.rs/tree/master/z3-sys

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

The [`z3-src` crate][z3-sys] contains the Z3 source distribution and logic to handle from-source builds.

## Z3 Version Compatibility

Versions of this library up to 0.19.x are compatible with Z3 4.8.12 through 4.16.0. 

This wide support comes at a cost: new low-level Z3 APIs must be gated behind feature flags or omitted entirely due to the developer burden.

Starting with version 0.20.0, this library will be tracking z3 releases more closely and will have a minimum supported Z3 version of 4.16.0. 

Backwards compatibility will be maintianed for as long as
Z3 does not break ABI compatibility by adding new exported enum variants,
new exported functions, or large semantic changes.

## When should I use `z3-sys` instead of `z3`?

The first scenario where it makes sense to use `z3-sys` directly is when some Z3
feature isn't wrapped into high-level bindings in the `z3` crate yet. In this
case, it is worth filing an issue and discussing its implementation in the `z3`
crate, but you can get at the raw, underlying features via the `z3-sys` crate in
the meantime.

The only other time to use `z3-sys` directly would be if you are writing your
own custom high-level API for Z3, instead of using the `z3` crate.
