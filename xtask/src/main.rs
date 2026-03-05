use std::path::{Path, PathBuf};
use std::process::Command;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    match std::env::args().nth(1).as_deref() {
        Some("gen-bindings") => gen_bindings()?,
        _ => {
            eprintln!("Usage: cargo xtask <task>");
            eprintln!();
            eprintln!("Tasks:");
            eprintln!("  gen-bindings    Regenerate z3-sys/src/generated/ from bundled Z3 headers");
            std::process::exit(1);
        }
    }
    Ok(())
}

fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is baked in at compile time and points to the xtask/
    // directory. The workspace root is its parent.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask manifest has no parent directory")
        .to_path_buf()
}

fn run(cmd: &mut Command) -> Result<(), Box<dyn std::error::Error>> {
    let status = cmd.status()?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("command failed: {cmd:?}").into())
    }
}

fn gen_bindings() -> Result<(), Box<dyn std::error::Error>> {
    let root = workspace_root();
    let header = root.join("z3-src/z3/src/api/z3.h");

    if !header.exists() {
        return Err(format!(
            "{} not found — did you init the z3-src submodule?\n  \
             git submodule update --init z3-src/z3",
            header.display()
        )
        .into());
    }

    // Force the build script to run unconditionally on the next build.
    run(Command::new("cargo")
        .args(["clean", "-p", "z3-sys"])
        .current_dir(&root))?;

    // Z3_SYS_UPDATE_GENERATED=1 causes build.rs to write the generated files
    // back to z3-sys/src/generated/ (the committed location) in addition to
    // the ephemeral Cargo output directory.
    run(Command::new("cargo")
        .args(["build", "-p", "z3-sys", "--features", "bindgen"])
        .env("Z3_SYS_Z3_HEADER", &header)
        .env("Z3_SYS_UPDATE_GENERATED", "1")
        .current_dir(&root))?;

    println!("Updated z3-sys/src/generated/functions.rs");
    println!("Updated z3-sys/src/generated/enums.rs");
    println!();
    println!("Review diffs with:   git diff z3-sys/src/generated/");
    println!("Check API coverage:  scripts/check-bindings.sh");

    Ok(())
}
