use crate::version::Version;

/// A Z3 version range over which an enum's committed numbering
/// (`src/generated/enums.rs`) is believed to be valid.
///
/// Z3 sometimes inserts new variants into the middle of a C enum instead of
/// appending them, which reassigns the numeric value of every later variant.
/// Bindgen only ever sees a single header snapshot, so this can't be
/// detected automatically — entries here are added by hand whenever such a
/// break is discovered (via Z3's changelog, a GitHub issue, or by diffing
/// `enums.rs` generated against two different Z3 versions).
pub(crate) struct EnumVersionRange {
    pub enum_name: &'static str,
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
        enum_name: "Z3_decl_kind",
        safe_min: version!(4, 8, 16),
        safe_max: None,
    },
    EnumVersionRange {
        // Z3 4.8.17 inserted SeqMap/SeqMapi/SeqFoldl/SeqFoldli into the
        // sequence range of Z3_decl_kind (values 1569-1572), shifting every
        // later string-operation variant (e.g. StrToInt) up by four.
        enum_name: "Z3_decl_kind",
        safe_min: version!(4, 8, 17),
        safe_max: None,
    },
];

/// Warns (via `cargo:warning`) about any known enum whose safe version range
/// doesn't cover `detected`. This is advisory only — it can't prove
/// compatibility, only flag known-risky combinations.
pub(crate) fn warn_on_mismatches(detected: Version) {
    for range in KNOWN_ENUM_VERSION_RANGES {
        let below_min = detected < range.safe_min;
        let above_max = range.safe_max.is_some_and(|max| detected > max);
        if below_min || above_max {
            println!(
                "cargo:warning=z3-sys: enum {} numbering may differ for Z3 {detected} \
                 (bindings assume Z3 >= {}); consider regenerating with the `bindgen` \
                 feature if you observe unexpected enum values.",
                range.enum_name, range.safe_min
            );
        }
    }
}
