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
Add it to your project with `cargo add`:

```bash 
$ cargo add z3-sys
```

### Finding Z3 Libraries

**Note:** This library has a dependency on Z3.

There are 4 ways for this crate to currently find Z3:

* By default, it will look for a system-installed copy of Z3.
  On Linux, this would be via the package manager. On macOS, this
  might be via Homebrew (`brew install z3`). Users can use
  the environment variable `Z3_LIBRARY_PATH_OVERRIDE` to manually
  specify the library search path.
* Enabling the `bundled` feature will use `cmake` to build and statically
  link Z3. This feature, as is, is only usable when `z3` or `z3-sys` is used
  as a `git` dependency, as it assumes the existence of a `git submodule` for
  Z3. Users wishing to use this feature with the release of `z3` or `z3-sys` on
  crates.io may optionally use the `Z3_SYS_BUNDLED_DIR_OVERRIDE` to point it to
  their own checkout of Z3.
* Enabling the `vcpkg` feature will use `vcpkg` to build and
  install a copy of Z3 which is then used.
* Enabling the `gh-release` feature will download a pre-compiled
  copy of Z3 from the GitHub release page for the current platform,
  if available.
  * You may specify the version of Z3 to download via the
  `Z3_SYS_Z3_VERSION` environment variable.
  * *Note: Github throttles unauthenticated requests from the
    same IP fairly aggressively.* If you are using the `gh-release` feature
    inside a CI pipeline (or if you `cargo clean` and rebuild a _lot_),
    you will likely experience random `403` responses downloading the
    `z3` build artifacts. To mitigate this, generate a read-only Personal
    Access Token (https://github.com/settings/personal-access-tokens) and
    provide it to the `READ_ONLY_GITHUB_TOKEN` environment variable. The
    `build.rs` step will automatically use this token (if present) to prevent
    throttling.

**Note:** This crate requires a `z3.h` during build time.

* By default, the crate will look for a `z3.h` in standard/system
  include paths. The `Z3_SYS_Z3_HEADER` environment variable can
  also be used to customize this.
* Enabling the`bundled` feature will cause the bundled copy of `z3.h`
  to be used. The `Z3_SYS_Z3_HEADER` environment variable can also
  be used to customize this.
* Enabling the `vcpkg` or `gh-release` feature will cause the copy of
  `z3.h` provided by that version to be used. In this case, there is
  no override via the environment variable.

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
