use std::fs;
use std::path::Path;

/// A parsed Z3 version (major.minor.patch).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Version {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// The minimum Z3 version z3-sys supports (Ubuntu 26.04's shipped Z3).
pub(crate) const MIN_SUPPORTED: Version = Version {
    major: 4,
    minor: 13,
    patch: 3,
};

/// Parses a dotted version string like `"4.13.3"` or `"4.13.3.0"`.
///
/// Extra trailing components (e.g. a build/tweak number) are ignored.
pub(crate) fn parse_dotted(s: &str) -> Option<Version> {
    let mut parts = s.trim().split('.');
    let major = parts.next()?.parse().ok()?;
    let minor = parts.next()?.parse().ok()?;
    let patch = parts.next().unwrap_or("0").parse().ok()?;
    Some(Version {
        major,
        minor,
        patch,
    })
}

/// Parses a Z3 version from a `z3_version.h` header, which defines
/// `Z3_MAJOR_VERSION`, `Z3_MINOR_VERSION`, and `Z3_BUILD_NUMBER` (the patch
/// component — Z3 does not call it `Z3_PATCH_VERSION`).
pub(crate) fn parse_header(path: &Path) -> Option<Version> {
    let contents = fs::read_to_string(path).ok()?;
    let major = find_macro_value(&contents, "Z3_MAJOR_VERSION")?;
    let minor = find_macro_value(&contents, "Z3_MINOR_VERSION")?;
    let patch = find_macro_value(&contents, "Z3_BUILD_NUMBER").unwrap_or(0);
    Some(Version {
        major,
        minor,
        patch,
    })
}

fn find_macro_value(contents: &str, name: &str) -> Option<u32> {
    for line in contents.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("#define") else {
            continue;
        };
        let mut tokens = rest.split_whitespace();
        if tokens.next() == Some(name) {
            return tokens.next()?.parse().ok();
        }
    }
    None
}
