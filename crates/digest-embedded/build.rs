//! On bare metal, puts the MPS2-AN386 memory map where cortex-m-rt's link.x
//! finds it: code in the 4 MiB SSRAM1 at 0x00000000, data in the 4 MiB SSRAM2/3
//! at 0x20000000, as QEMU's `mps2-an386` machine maps them.

use std::{env, fs, path::PathBuf};

fn main() {
    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("none") {
        return;
    }
    let out = PathBuf::from(env::var("OUT_DIR").expect("cargo sets OUT_DIR"));
    fs::write(
        out.join("memory.x"),
        "MEMORY\n{\n  FLASH : ORIGIN = 0x00000000, LENGTH = 4M\n  RAM : ORIGIN = 0x20000000, LENGTH = 4M\n}\n",
    )
    .expect("OUT_DIR is writable");
    println!("cargo:rustc-link-search={}", out.display());
    println!("cargo:rustc-link-arg-bins=-Tlink.x");
    println!("cargo:rerun-if-changed=build.rs");
}
