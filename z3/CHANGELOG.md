# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.14.3](https://github.com/prove-rs/z3.rs/compare/z3-v0.14.2...z3-v0.14.3) - 2025-08-18

### Fixed

- decrement vectors after get_consequences is done with them ([#414](https://github.com/prove-rs/z3.rs/pull/414)) (by @Pat-Lafon) - #414

### Other

- reorganize ast module ([#411](https://github.com/prove-rs/z3.rs/pull/411)) (by @toolCHAINZ) - #411

### Contributors

* @Pat-Lafon
* @toolCHAINZ

## [0.14.2](https://github.com/prove-rs/z3.rs/compare/z3-v0.14.1...z3-v0.14.2) - 2025-08-14

### Added

- add bundled path override ([#408](https://github.com/prove-rs/z3.rs/pull/408)) (by @toolCHAINZ)

### Contributors

* @toolCHAINZ

## [0.14.1](https://github.com/prove-rs/z3.rs/compare/z3-v0.14.0...z3-v0.14.1) - 2025-08-09

### Added

- enable moving and referencing z3 types between threads ([#404](https://github.com/prove-rs/z3.rs/pull/404)) (by @toolCHAINZ) - #404
- impl default for context ([#402](https://github.com/prove-rs/z3.rs/pull/402)) (by @toolCHAINZ) - #402

### Contributors

* @toolCHAINZ

## [0.14.0](https://github.com/prove-rs/z3.rs/compare/z3-v0.13.3...z3-v0.14.0) - 2025-08-06

### Added

- add BV::from_bits  ([#398](https://github.com/prove-rs/z3.rs/pull/398)) (by @Evian-Zhang) - #398
- Bump to Rust 2024 edition ([#381](https://github.com/prove-rs/z3.rs/pull/381)) (by @Evian-Zhang) - #381

### Changed

- [**breaking**] refcount z3 context ([#401](https://github.com/prove-rs/z3.rs/pull/401)) (by @toolCHAINZ) - #401

### Fixed

- [**breaking**] make argument of `Probe::lt` consistent with other comparison operations (by @mehrad31415) - #391
- make BV::from_bits return Option ([#399](https://github.com/prove-rs/z3.rs/pull/399)) (by @toolCHAINZ) - #399

### Contributors

* @toolCHAINZ
* @Evian-Zhang
* @mehrad31415

## [0.13.3](https://github.com/prove-rs/z3.rs/compare/z3-v0.13.2...z3-v0.13.3) - 2025-07-17

### Added

- Add Z3_LIBRARY_PATH_OVERRIDE ([#377](https://github.com/prove-rs/z3.rs/pull/377)) (by @Evian-Zhang) - #377

### Contributors

* @Evian-Zhang

## [0.13.2](https://github.com/prove-rs/z3.rs/compare/z3-v0.13.1...z3-v0.13.2) - 2025-07-14

### Fixed

- Make translate 'dst lifetime independent of 'ctx ([#365](https://github.com/prove-rs/z3.rs/pull/365)) (by @toolCHAINZ) - #365

### Other

- Better documentation of z3 installation options ([#364](https://github.com/prove-rs/z3.rs/pull/364)) (by @lmondada) - #364

### Contributors

* @toolCHAINZ
* @lmondada

## [0.13.1](https://github.com/prove-rs/z3.rs/compare/z3-v0.13.0...z3-v0.13.1) - 2025-07-10

### Added

- add gh-release feature to get z3 from released libraries ([#352](https://github.com/prove-rs/z3.rs/pull/352))

## [0.13.0](https://github.com/prove-rs/z3.rs/compare/z3-v0.12.1...z3-v0.13.0) - 2025-07-10

### Added

- atmost and atleast ([#320](https://github.com/prove-rs/z3.rs/pull/320))

### Other

- Update crate READMEs to use `cargo add` and update example to not require updating for every version change
- Fix `mismatched_lifetime_syntaxes` lints ([#354](https://github.com/prove-rs/z3.rs/pull/354))
- Fix some `clippy::uninlined_format_args` lints ([#353](https://github.com/prove-rs/z3.rs/pull/353))
- Panic through rust if provided an invalid tactic str to prevent SIGSEGV ([#339](https://github.com/prove-rs/z3.rs/pull/339))
- Add is_infinite, is_normal, is_subnormal, is_zero, is_nan to Float ([#336](https://github.com/prove-rs/z3.rs/pull/336))
- Make `z3_ctx` `pub` ([#341](https://github.com/prove-rs/z3.rs/pull/341))
- Fix CI ([#329](https://github.com/prove-rs/z3.rs/pull/329))
- Add high-level binding for quantifier creation with additional attributes ([#326](https://github.com/prove-rs/z3.rs/pull/326))
- Add bindings for seq.++ and seq.unit ([#323](https://github.com/prove-rs/z3.rs/pull/323))
- Adjust lifetimes on `ModelIter` to make them more permissive ([#324](https://github.com/prove-rs/z3.rs/pull/324))
- Add binding for FPA to IEEE-754 bit-vector ([#322](https://github.com/prove-rs/z3.rs/pull/322))
- Add binding for str.substr ([#321](https://github.com/prove-rs/z3.rs/pull/321))
- Add binding to get unit string at index ([#319](https://github.com/prove-rs/z3.rs/pull/319))
- Add high-level binding for string length ([#318](https://github.com/prove-rs/z3.rs/pull/318))
- Expose sequence sort and AST ([#310](https://github.com/prove-rs/z3.rs/pull/310))
- Add high-level binding to create lambda consts ([#311](https://github.com/prove-rs/z3.rs/pull/311))
- Support consequences API ([#302](https://github.com/prove-rs/z3.rs/pull/302)) ([#308](https://github.com/prove-rs/z3.rs/pull/308))
- Real approx functions ([#304](https://github.com/prove-rs/z3.rs/pull/304))
- Z3 Optimize: add `assert_and_track` and `get_unsat_core` ([#300](https://github.com/prove-rs/z3.rs/pull/300))
- Support for more regular expression operations ([#275](https://github.com/prove-rs/z3.rs/pull/275))
- Expose underlying Z3_context and Z3_sort ([#298](https://github.com/prove-rs/z3.rs/pull/298))
- Expose Z3_get_version in the high-level interface
- [deps] Bump env_logger to 0.11
- add parameter configuration API
- add new_const and fresh_const functions to Dynamic
- fix array_range and array_domain lifetimes
- Fix doc comment typo.
- Implement += for Solver
- Expose API to convert solver into SMT-LIB2 format ([#267](https://github.com/prove-rs/z3.rs/pull/267))
- Add doc comment to Z3_solver_get_unsat_core.
- Add a warning when `static-link-z3` is used.
- Rename `static-link-z3` to `bundled`.
- Fix `semicolon_if_nothing_returned` lints.
- Fix lifetime on `Solver::get_assertions()` result.
- Implement `ast::Float::as_f64`
- Remove usage of `extern crate`.
- Always use `num`, remove `arbitrary-size-numeral` feature.
- Update to Rust edition 2018. Collapse some imports.
- Inline format args.
- Add vcpkg support and corresponding CI. ([#251](https://github.com/prove-rs/z3.rs/pull/251))
- Enable `doc_markdown` lint.
- Fix typo: "sufix" -> "suffix"
- Add backticks around logic expression.
- Add is_const_array
- Have distinct take impl Borrow
- Fix clippy::doc_markdown warnings.
- Fix redundant_pattern_matching warning.
- Add comment
- Use Borrow in varop arrays
- Check Kind for optimize maximize
