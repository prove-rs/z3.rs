use std::env;

/// Version thresholds that gate specific APIs. Add an entry here alongside
/// the `#[cfg(z3_{major}_{minor})]` attribute(s) it controls.
const KNOWN_THRESHOLDS: &[(u32, u32)] = &[
    (4, 16), // Optimize::solutions(), Translate/Clone for Optimize (see src/optimize.rs)
];

fn main() {
    // Declare every cfg we might emit up front, regardless of which branch
    // below runs, so `-D warnings` never trips on `unexpected_cfgs`.
    for (major, minor) in KNOWN_THRESHOLDS {
        println!("cargo::rustc-check-cfg=cfg(z3_{major}_{minor})");
    }
    println!("cargo::rustc-check-cfg=cfg(z3_version_major, values(any()))");
    println!("cargo::rustc-check-cfg=cfg(z3_version_minor, values(any()))");

    println!("cargo:rerun-if-env-changed=DOCS_RS");
    println!("cargo:rerun-if-env-changed=DEP_Z3_VERSION_MAJOR");
    println!("cargo:rerun-if-env-changed=DEP_Z3_VERSION_MINOR");

    let (major, minor) = if env::var_os("DOCS_RS").is_some() {
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
    for (t_major, t_minor) in KNOWN_THRESHOLDS {
        if (major, minor) >= (*t_major, *t_minor) {
            println!("cargo::rustc-cfg=z3_{t_major}_{t_minor}");
        }
    }
}

/// Reads the Z3 version z3-sys detected, via the `links = "z3"` metadata
/// passthrough (`DEP_Z3_VERSION_MAJOR`/`MINOR`, emitted by z3-sys/build.rs).
fn read_dep_z3_version() -> (u32, u32) {
    let major = env::var("DEP_Z3_VERSION_MAJOR")
        .ok()
        .and_then(|s| s.parse().ok());
    let minor = env::var("DEP_Z3_VERSION_MINOR")
        .ok()
        .and_then(|s| s.parse().ok());
    match (major, minor) {
        (Some(major), Some(minor)) => (major, minor),
        _ => {
            println!(
                "cargo:warning=z3: could not read the Z3 version detected by z3-sys \
                 (DEP_Z3_VERSION_MAJOR/MINOR); version-gated APIs will be unavailable."
            );
            (0, 0)
        }
    }
}
