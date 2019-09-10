use std::path::PathBuf;
use std::{env, fs};

fn main() {
    // Put the linker script somewhere the linker can find it
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());

    fs::write(
        out.join("link-userapp.x"),
        &include_bytes!("link-userapp.x")[..],
    )
    .unwrap();

    println!("cargo:rustc-link-search={}", out.display());

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=link-userapp.x");
}
