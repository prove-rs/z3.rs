use crate::version::Version;

/// A Z3 version range over which the committed enum numbering
/// (`src/generated/enums.rs`) is believed to be stable.
///
/// Z3 sometimes inserts new variants into the middle of a C enum instead of
/// appending them, which reassigns the numeric value of every later variant.
/// Bindgen only ever sees a single header snapshot, so this can't be
/// detected automatically — ranges here are added by hand whenever such a
/// break is discovered (via Z3's changelog, a GitHub issue, or by diffing
/// `enums.rs` generated against two different Z3 versions).
///
/// `KNOWN_ENUM_VERSION_RANGES` must be sorted ascending by `safe_min` and
/// cover every released Z3 version with no gaps or overlaps: each range's
/// `safe_max` is the last version known to share that numbering, and the
/// next range's `safe_min` is the version that broke it. The final range has
/// `safe_max: None` and its `safe_min` is the version `enums.rs` was
/// actually generated from — i.e. the current bin.
pub(crate) struct EnumVersionRange {
    pub safe_min: Version,
    pub safe_max: Option<Version>,
}

macro_rules! version {
    ($major:expr, $minor:expr, $patch:expr) => {
        Version {
            major: $major,
            minor: $minor,
            patch: $patch,
        }
    };
}

pub(crate) const KNOWN_ENUM_VERSION_RANGES: &[EnumVersionRange] = &[
    EnumVersionRange {
        // Z3_OP_RECURSIVE was inserted in the middle of Z3_decl_kind (rather
        // than appended) by commit c9fa00a, shifting the numeric value of
        // every later Z3_OP_* variant. Released in Z3 4.8.16.
        // See https://github.com/Z3Prover/z3/issues/6030.
        // Stable through 4.13.0 (the last release before the next break).
        safe_min: version!(4, 8, 16),
        safe_max: Some(version!(4, 13, 0)),
    },
    EnumVersionRange {
        // Z3 4.13.2 inserted Z3_OP_ABS and SeqMap/SeqMapi/SeqFoldl/SeqFoldli
        // into the sequence range of Z3_decl_kind (values 1569-1572),
        // shifting every later string-operation variant (e.g. StrToInt) up
        // by four. Introduced by commit fc6c4c98e ("initial warppers for
        // seq-map/seq-fold"). Stable through 4.14.0.
        safe_min: version!(4, 13, 2),
        safe_max: Some(version!(4, 14, 0)),
    },
    EnumVersionRange {
        // Z3 4.14.1 inserted Z3_OP_SBV2INT into the bitvector range of
        // Z3_decl_kind, shifting Z3_OP_CARRY, Z3_OP_XOR3, and 8 other later
        // variants up by one. Stable through 4.16.0.
        safe_min: version!(4, 14, 1),
        safe_max: Some(version!(4, 16, 0)),
    },
    EnumVersionRange {
        // Z3 5.0.0 inserted 13 Z3_OP_FINITE_SET_* variants into
        // Z3_decl_kind before Z3_OP_INTERNAL, shifting Z3_OP_INTERNAL,
        // Z3_OP_RECURSIVE, and Z3_OP_UNINTERPRETED from 45100-45102 to
        // 49165-49167. This is the numbering currently committed in
        // src/generated/enums.rs.
        safe_min: version!(5, 0, 0),
        safe_max: None,
    },
];

/// Warns (via `cargo:warning`) if `detected` falls outside the version era
/// the committed enum numbering was generated from. This is advisory only —
/// it can't prove compatibility, only flag a known-risky combination.
pub(crate) fn warn_on_mismatches(detected: Version) {
    let Some(current) = KNOWN_ENUM_VERSION_RANGES
        .iter()
        .find(|r| r.safe_max.is_none())
    else {
        return;
    };
    if detected >= current.safe_min {
        return;
    }
    println!(
        "cargo:warning=z3-sys: some enum numbering (e.g. Z3_decl_kind) may differ for Z3 \
         {detected}; bindings were generated for Z3 >= {}. Consider regenerating with the \
         `bindgen` feature if you observe unexpected enum values.",
        current.safe_min
    );
}
