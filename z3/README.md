# z3

[![](http://meritbadge.herokuapp.com/z3)](https://crates.io/crates/z3)

High-level rust bindings to the Z3 SMT solver

Licensed under the MIT license.

See [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3) for details on Z3.

## Documentation

The API is fully documented with examples:
[https://docs.rs/z3/](https://docs.rs/z3/)

## Installation

This crate works with Cargo and is on
[crates.io](https://crates.io/crates/z3).
Add it to your `Cargo.toml` like so:

```toml
[dependencies]
z3 = "0.6.0"
```

**Note:** This library has a dependency on Z3. You will either need to
have the Z3 dependency already installed, or you can statically link
to our build of Z3 like so:

```toml
[dependencies]
z3 = {version="0.6.0", features = ["static-link-z3"]}
```

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
