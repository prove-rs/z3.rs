# `z3` and `z3-sys`

[![Rust](https://github.com/prove-rs/z3.rs/actions/workflows/rust.yml/badge.svg)](https://github.com/prove-rs/z3.rs/actions/workflows/rust.yml)

This repository contains [high-level][z3] and [low-level][z3-sys] Rust bindings
for the [Z3 solver][upstream].

[upstream]: https://github.com/Z3Prover/z3
[z3]: https://github.com/prove-rs/z3.rs/tree/master/z3
[z3-sys]: https://github.com/prove-rs/z3.rs/tree/master/z3-sys

## `z3`

[![](http://meritbadge.herokuapp.com/z3)](https://crates.io/crates/z3)

The [`z3` crate][z3] provides high-level bindings to the Z3 solver. It is built
on top of, and wraps, the `z3-sys` crate. This is the crate you'll want to use
99% of the time.

## `z3-sys`

[![](http://meritbadge.herokuapp.com/z3-sys)](https://crates.io/crates/z3-sys)

The [`z3-sys` crate][z3-sys] provides the raw, unsafe, low-level C API that Z3
exposes.

## When should I use `z3-sys` instead of `z3`?

The first scenario where it makes sense to use `z3-sys` directly is when some Z3
feature isn't wrapped into high-level bindings in the `z3` crate yet. In this
case, it is worth filing an issue and discussing its implementation in the `z3`
crate, but you can get at the raw, underlying features via the `z3-sys` crate in
the meantime.

The only other time to use `z3-sys` directly would be if you are writing your
own custom high-level API for Z3, instead of using the `z3` crate.

## Release Process

1. Make a version bump commit
    1. Bump version for the relevant crate in Cargo.toml
    1. Update version in examples/READMEs
1. Create a git tag for the commit
    1. i.e. `git tag z3-v0.10.0`
1. Push the changes
    1. `git push`
    1. `git push --tags`
1. Publish on crates.io
    1. `cargo publish`
