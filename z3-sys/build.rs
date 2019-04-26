use std::env;
use std::fs::{copy, create_dir, read_dir};
use std::path::{Path, PathBuf};
use std::process::Command;

fn update_dir(from: &Path, to: &Path) {
    if !to.exists() {
        create_dir(to).expect(&format!("Failed to create directory {}", to.display()));
    }

    for entry in read_dir(from).expect(&format!("Unable to open directory {}", from.display())) {
        let entry = entry.unwrap();
        let path = entry.path();

        println!("cargo:rerun-if-changed={}", path.display());

        let path = path.file_name().unwrap();
        let from_path = from.join(&path);
        let to_path = to.join(path);

        if !to_path.exists()
            || entry.metadata().unwrap().modified().unwrap()
                > to_path.metadata().unwrap().modified().unwrap()
        {
            if entry.metadata().unwrap().is_file() {
                copy(from_path, to_path).unwrap();
            } else {
                update_dir(from_path.as_path(), to_path.as_path());
            }
        }
    }
}

fn main() {
    let out_path = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));

    update_dir(Path::new("../vendor"), &out_path.join("vendor"));
    Command::new("python")
        .arg("scripts/mk_make.py")
        .current_dir(out_path.join("vendor"))
        .arg(format!(
            "--prefix={}",
            out_path.join("vendor_install").display()
        ))
        .output()
        .expect("Unable to generate makefiles");
    Command::new("make")
        .arg("install")
        .current_dir(out_path.join("vendor").join("build"))
        .output()
        .expect("Unable to install z3");

    println!("cargo:rustc-link-lib=z3");

    let bindings = bindgen::Builder::default()
        .header("src/wrapper.h")
        .clang_arg(format!(
            "-I{}",
            out_path.join("vendor_install").join("include").display()
        ))
        .prepend_enum_name(false)
        .blacklist_item("Z3_TRUE")
        .blacklist_item("Z3_FALSE")
        .generate()
        .expect("Unable to generate bindings");

    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
