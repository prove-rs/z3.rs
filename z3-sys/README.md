# z3-sys

[![](https://img.shields.io/crates/v/z3-sys.svg)](https://crates.io/crates/z3-sys)

Low-level rust bindings to the Z3 SMT solver

Licensed under the MIT license.

See [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3) for details on Z3.

## Documentation

The API is fully documented with examples:
[https://docs.rs/z3-sys/](https://docs.rs/z3-sys/)

## Installation

This crate works with Cargo and is on
[crates.io](https://crates.io/crates/z3-sys).
Add it to your `Cargo.toml` like so:

```toml
[dependencies]
z3-sys = "0.8"
```

**Note:** This crate requires a `z3.h` during build time.

* By default, the crate will look for a `z3.h` in standard/system include paths.
* If the feature `bundled-z3` is enabled, the `z3.h` of the built Z3 will be used.
* If the feature `vcpkg` is enabled, the `z3.h` of the built Z3 in vcpkg will be used.
  Please note that [vcpkg-rs](https://docs.rs/vcpkg-rs) uses `*-windows-static-md` on Windows platform by default.
* Alternatively, the path to the desired `z3.h` can be specified via the environment variable
`Z3_SYS_Z3_HEADER`. I.e., running:

```console
$ Z3_SYS_Z3_HEADER="/path/to/my/z3.h" cargo build
```

in your project will use `/path/to/my/z3.h` instead.

## Support and Maintenance

I am developing this library largely on my own so far. I am able
to offer support and maintenance, but would very much appreciate
donations via [Patreon](https://patreon.com/endoli). I can also
provide commercial support, so feel free to
[contact me](mailto:bruce.mitchener@gmail.com).

## Contribution

Unless you explicitly state otherwise, any contribution
intentionally submitted for inclusion in the work by you,
shall be dual licensed as above, without any additional
terms or conditions.
