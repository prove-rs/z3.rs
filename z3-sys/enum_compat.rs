use crate::version::Version;

/// A Z3 version at which the committed enum numbering
/// (`src/generated/enums.rs`) is known to have changed.
///
/// Z3 sometimes inserts new variants into the middle of a C enum instead of
/// appending them, which reassigns the numeric value of every later variant.
/// Bindgen only ever sees a single header snapshot, so this can't be
/// detected automatically — entries here are added by hand whenever such a
/// break is discovered (via Z3's changelog, a GitHub issue, or by diffing
/// `enums.rs` generated against two different Z3 versions).
///
/// `KNOWN_ENUM_BREAKS` must be sorted ascending. The last entry is the
/// version `enums.rs` was actually generated from — i.e. the current bin.
macro_rules! version {
    ($major:expr, $minor:expr, $patch:expr) => {
        Version {
            major: $major,
            minor: $minor,
            patch: $patch,
        }
    };
}

pub(crate) const KNOWN_ENUM_BREAKS: &[Version] = &[
    // Z3_OP_RECURSIVE was inserted in the middle of Z3_decl_kind (rather
    // than appended) by commit c9fa00a, shifting the numeric value of
    // every later Z3_OP_* variant. Released in Z3 4.8.16.
    // See https://github.com/Z3Prover/z3/issues/6030.
    version!(4, 8, 16),
    // Z3 4.13.2 inserted Z3_OP_ABS and SeqMap/SeqMapi/SeqFoldl/SeqFoldli
    // into the sequence range of Z3_decl_kind (values 1569-1572),
    // shifting every later string-operation variant (e.g. StrToInt) up
    // by four. Introduced by commit fc6c4c98e ("initial warppers for
    // seq-map/seq-fold").
    version!(4, 13, 2),
    // Z3 4.14.1 inserted Z3_OP_SBV2INT into the bitvector range of
    // Z3_decl_kind, shifting Z3_OP_CARRY, Z3_OP_XOR3, and 8 other later
    // variants up by one.
    version!(4, 14, 1),
    // Z3 5.0.0 inserted 13 Z3_OP_FINITE_SET_* variants into
    // Z3_decl_kind before Z3_OP_INTERNAL, shifting Z3_OP_INTERNAL,
    // Z3_OP_RECURSIVE, and Z3_OP_UNINTERPRETED from 45100-45102 to
    // 49165-49167. This is the numbering currently committed in
    // src/generated/enums.rs.
    version!(5, 0, 0),
];

/// Warns (via `cargo:warning`) if `detected` falls outside the version era
/// the committed enum numbering was generated from. This is advisory only —
/// it can't prove compatibility, only flag a known-risky combination.
pub(crate) fn warn_on_mismatches(detected: Version) {
    let Some(&current) = KNOWN_ENUM_BREAKS.last() else {
        return;
    };
    if detected >= current {
        return;
    }
    println!(
        "cargo:warning=z3-sys: attempting to link against Z3 {detected} with `z3-sys` bindings for Z3 >= {current}; \
         enum numbering (e.g. Z3_decl_kind) may differ across these versions. \
         Consider updating Z3 or else enabling the `bindgen` feature to ensure compatibility.",
    );
}
