use std::env;

/// Version thresholds that gate specific APIs. Add an entry here alongside
/// the `#[cfg(z3_{major}_{minor}_{patch})]` attribute(s) it controls.
///
/// Z3 doesn't treat its version number as an API-stability contract: new C
/// API functions have landed in patch releases (e.g. `Z3_mk_abs` in 4.13.2,
/// several `Z3_mk_seq_*` functions across 4.15.3-4.15.5), so thresholds here
/// must be exact `(major, minor, patch)` triples, not just `(major, minor)`.
const KNOWN_THRESHOLDS: &[(u32, u32, u32)] = &[
    (4, 16, 0), // Optimize::solutions(), Translate/Clone for Optimize (see src/optimize.rs)
];

fn main() {
    // Declare every cfg we might emit up front, regardless of which branch
    // below runs, so `-D warnings` never trips on `unexpected_cfgs`.
    for (major, minor, patch) in KNOWN_THRESHOLDS {
        println!("cargo::rustc-check-cfg=cfg(z3_{major}_{minor}_{patch})");
    }
    println!("cargo::rustc-check-cfg=cfg(z3_version_major, values(any()))");
    println!("cargo::rustc-check-cfg=cfg(z3_version_minor, values(any()))");
    println!("cargo::rustc-check-cfg=cfg(z3_version_patch, values(any()))");

    println!("cargo:rerun-if-env-changed=DOCS_RS");
    println!("cargo:rerun-if-env-changed=DEP_Z3_VERSION_MAJOR");
    println!("cargo:rerun-if-env-changed=DEP_Z3_VERSION_MINOR");
    println!("cargo:rerun-if-env-changed=DEP_Z3_VERSION_PATCH");

    let (major, minor, patch) = if env::var_os("DOCS_RS").is_some() {
        // docs.rs never links a real Z3 (z3-sys's own detection falls back to
        // its minimum-supported version in that environment), so force
        // "assume the latest known threshold" here instead, so every
        // version-gated API still renders in the published docs.
        *KNOWN_THRESHOLDS
            .iter()
            .max()
            .expect("KNOWN_THRESHOLDS is non-empty")
    } else {
        read_dep_z3_version()
    };

    println!("cargo::rustc-cfg=z3_version_major=\"{major}\"");
    println!("cargo::rustc-cfg=z3_version_minor=\"{minor}\"");
    println!("cargo::rustc-cfg=z3_version_patch=\"{patch}\"");
    for (t_major, t_minor, t_patch) in KNOWN_THRESHOLDS {
        if (major, minor, patch) >= (*t_major, *t_minor, *t_patch) {
            println!("cargo::rustc-cfg=z3_{t_major}_{t_minor}_{t_patch}");
        }
    }
}

/// Reads the Z3 version z3-sys detected, via the `links = "z3"` metadata
/// passthrough (`DEP_Z3_VERSION_MAJOR`/`MINOR`/`PATCH` in `z3/build.rs`),
/// emitted by z3-sys/build.rs.
fn read_dep_z3_version() -> (u32, u32, u32) {
    let major = env::var("DEP_Z3_VERSION_MAJOR")
        .ok()
        .and_then(|s| s.parse().ok());
    let minor = env::var("DEP_Z3_VERSION_MINOR")
        .ok()
        .and_then(|s| s.parse().ok());
    let patch = env::var("DEP_Z3_VERSION_PATCH")
        .ok()
        .and_then(|s| s.parse().ok());
    match (major, minor, patch) {
        (Some(major), Some(minor), Some(patch)) => (major, minor, patch),
        _ => {
            println!(
                "cargo:warning=z3: could not read the Z3 version detected by z3-sys \
                 (DEP_Z3_VERSION_MAJOR/MINOR/PATCH); version-gated APIs will be unavailable."
            );
            (0, 0, 0)
        }
    }
}
