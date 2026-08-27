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

Starting with version 0.20.0, z3-rs aims to track the latest Z3 release and stay up-to-date with API changes.

| z3      | z3-sys   | upstream Z3                                          |
|---------|----------|-------------------------------------------------------|
| ≤0.19.x | ≤0.10.x  | ≥4.8.12                                              |
| ≥0.20.0 | ≥0.11.0  | ≥4.13.3 (auto-detected; ≥4.16.0 for `Optimize::translate`/`Clone`) |

### ≤0.19.x (z3-sys ≤0.10.x): broad version support

Function and opaque structure FFI bindings were generated and committed sometime around Z3 4.8.12
and updated ad-hoc, but enum bindings were re-generated via bindgen on every build.
This let the enums track whatever Z3 version was linked, giving broad 4.8.12–4.16.0 support. The cost was
that new high-level Z3 APIs could not easily be defined without feature-gating, and were often
omitted entirely.

### ≥0.20.0 (z3-sys ≥0.11.0): static generated bindings

Both functions and enums are tracked in version control
(`z3-sys/src/generated/functions.rs` and `z3-sys/src/generated/enums.rs`). There is by default no
dynamic bindgen step on every build.

The minimum supported upstream Z3 version is **4.13.3** (the version shipped by Ubuntu 26.04),
enforced automatically: `z3-sys`'s build script detects the linked Z3 version (from
`z3_version.h`, pkg-config, vcpkg, or the `Z3_SYS_Z3_VERSION` env var, in that priority order)
and fails the build with an actionable error if it's below the minimum. If the version can't be
detected at all (e.g. no Z3 installed yet), the build assumes the minimum and warns, rather than
failing — so `cargo check`/rust-analyzer keep working on a fresh checkout.

APIs that require a newer Z3 than the minimum are gated behind auto-derived `cfg`s instead of
Cargo features, so no manual opt-in is needed and editor tooling picks them up correctly.
**`Optimize::translate` and `Optimize::clone` require Z3 ≥ 4.16.0** (`Z3_optimize_translate` was
added in that release) and are gated behind `#[cfg(z3_4_16)]`, which `z3/build.rs` sets
automatically once it observes a linked Z3 ≥ 4.16.0 — no feature flag or configuration needed.

Z3 has, on occasion, inserted new variants into the middle of a C enum instead of appending them
(e.g. Z3 4.8.16 inserted `Z3_OP_RECURSIVE` into `Z3_decl_kind`, 4.13.2 inserted
`SeqMap`/`SeqMapi`/`SeqFoldl`/`SeqFoldli`, 4.14.1 inserted `Z3_OP_SBV2INT`, and 5.0.0 inserted
13 `Z3_OP_FINITE_SET_*` variants, each shifting the numeric value of every later variant).
`z3-sys/build.rs` keeps a hand-maintained table of such known changes (`z3-sys/enum_compat.rs`)
and warns if the detected version falls outside a recorded safe range. The 4.13.2 and 4.14.1
breaks are both below the current bundled/committed numbering (Z3 5.0.0), so a linked Z3 anywhere
from the 4.13.3 minimum up to (but not including) 5.0.0 has incorrect `Z3_OP_INTERNAL`,
`Z3_OP_RECURSIVE`, and `Z3_OP_UNINTERPRETED` values — `enum_compat.rs` will warn in that case.

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
