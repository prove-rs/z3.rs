use std::path::{Path, PathBuf};
use std::process::Command;

use clap::{Parser, Subcommand};
use semver::Version;

#[derive(Parser)]
#[command(about = "z3.rs workspace task runner")]
struct Cli {
    #[command(subcommand)]
    command: CliCommand,
}

#[derive(Subcommand)]
enum CliCommand {
    /// Regenerate z3-sys/src/generated/ from vendored Z3 headers.
    GenBindings,
    /// Check out a Z3 tag in the submodule and update Cargo.toml versions.
    PrepareZ3Src {
        /// Z3 git tag to check out, e.g. `z3-4.16.1` or `4.16.1`.
        z3_tag: String,
    },
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    match cli.command {
        CliCommand::GenBindings => gen_bindings()?,
        CliCommand::PrepareZ3Src { z3_tag } => prepare_z3_src(&z3_tag)?,
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

    Ok(())
}

fn read_z3_version(submodule: &Path) -> Result<Version, Box<dyn std::error::Error>> {
    let version_txt = submodule.join("scripts/VERSION.txt");
    let version_str = std::fs::read_to_string(&version_txt)
        .map_err(|e| format!("failed to read {}: {e}", version_txt.display()))?
        .trim()
        .to_string();
    let periods = version_str.split_terminator(|p| ".".contains(p)).count();
    let version_str = if periods > 2 {
        // we have extra periods: trim all but the most major versions
        let new_str = version_str
            .split(|p| ".".contains(p))
            .take(3)
            .collect::<Vec<_>>()
            .join(".");
        println!("Trimming Z3 reported version {version_str} to {new_str}");
        new_str
    } else {
        version_str
    };
    Version::parse(version_str.trim()).map_err(|e| {
        format!(
            "unexpected VERSION.txt content {:?}: {e}",
            version_str.trim()
        )
        .into()
    })
}

fn prepare_z3_src(z3_tag: &str) -> Result<(), Box<dyn std::error::Error>> {
    let root = workspace_root();

    // 1. Normalise tag: accept both `z3-4.16.1` and `4.16.1`.
    let display_version = z3_tag.strip_prefix("z3-").unwrap_or(z3_tag);
    let git_tag = if z3_tag.starts_with("z3-") {
        z3_tag.to_string()
    } else {
        format!("z3-{z3_tag}")
    };

    // 2. Submodule init + checkout.
    run(Command::new("git")
        .args(["submodule", "update", "--init", "z3-src/z3"])
        .current_dir(&root))?;

    let submodule = root.join("z3-src/z3");
    run(Command::new("git")
        .arg("-C")
        .arg(&submodule)
        // Forcing here because Z3 overwrites their nightly tag
        .args(["fetch", "--tags", "origin", "--force"]))?;
    run(Command::new("git")
        .arg("-C")
        .arg(&submodule)
        .args(["checkout", &git_tag]))?;

    // 3. Parse VERSION.txt → compute crate version.
    let z3_ver = read_z3_version(&submodule)?;
    let crate_version = format!("{}{:02}.{}.0", z3_ver.major, z3_ver.minor, z3_ver.patch);
    let series = format!("{}{:02}", z3_ver.major, z3_ver.minor);

    println!("Z3 version:    {display_version}");
    println!("crate version: {crate_version}");
    println!("series:        {series}");
    println!();

    // 4. Edit Cargo.toml files.
    let z3_src_toml = root.join("z3-src/Cargo.toml");
    let z3_sys_toml = root.join("z3-sys/Cargo.toml");

    let current_z3src_ver = read_package_version(&z3_src_toml)?;
    set_toml_field(
        &z3_src_toml,
        &format!("version = \"{current_z3src_ver}\""),
        &format!("version = \"{crate_version}\""),
    )?;

    let current_series = read_z3src_dep_series(&z3_sys_toml)?;
    set_toml_field(
        &z3_sys_toml,
        &format!("z3-src = {{ version = \"{current_series}\", optional = true }}"),
        &format!("z3-src = {{ version = \"{series}\", optional = true }}"),
    )?;

    // 5. Post-action guidance.
    println!("Prepared z3-src {crate_version} (Z3 {display_version})");
    println!();
    println!("Review changes:");
    println!("  git diff z3-src/Cargo.toml z3-sys/Cargo.toml");
    println!("  git -C z3-src/z3 log --oneline -3");
    println!();
    println!("Commit and open a PR. release-plz will publish on merge.");

    Ok(())
}

/// Replaces the first occurrence of `old` with `new` in the file at `path`.
/// Returns an error if `old` is not found (guards against silent no-ops).
fn set_toml_field(path: &Path, old: &str, new: &str) -> Result<(), Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    if !content.contains(old) {
        return Err(format!(
            "{}: pattern not found: {:?}\n  (file may already be updated or format has changed)",
            path.display(),
            old
        )
        .into());
    }
    let updated = content.replacen(old, new, 1);
    std::fs::write(path, updated)?;
    Ok(())
}

/// Returns the value of the first `version = "..."` field in a Cargo.toml.
fn read_package_version(path: &Path) -> Result<String, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    for line in content.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("version = \"")
            && let Some(ver) = rest.strip_suffix('"')
        {
            return Ok(ver.to_string());
        }
    }
    Err(format!("no `version = \"...\"` field found in {}", path.display()).into())
}

/// Returns the version string from the `z3-src = { version = "...", ... }` dep line.
fn read_z3src_dep_series(path: &Path) -> Result<String, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    for line in content.lines() {
        if !line.trim_start().starts_with("z3-src = {") {
            continue;
        }
        if let Some((_, after)) = line.split_once("version = \"")
            && let Some((ver, _)) = after.split_once('"')
        {
            return Ok(ver.to_string());
        }
    }
    Err(format!("no `z3-src` dep with version found in {}", path.display()).into())
}
