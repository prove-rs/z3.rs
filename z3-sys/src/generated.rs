// These files are pre-generated from the pinned Z3 source in z3-src/z3.
// To regenerate after bumping the z3-src submodule, run:
//   Z3_SYS_UPDATE_GENERATED=1 cargo build -p z3-sys --features bindgen,bundled

#[cfg(not(feature = "bindgen"))]
include!("generated/enums.rs");

#[cfg(feature = "bindgen")]
include!(concat!(env!("OUT_DIR"), "/enums.rs"));
