//! Computes the determinism digest and compares it with the committed value.
//!
//! On a bare-metal target it runs from reset under QEMU (`mps2-an386`, a
//! Cortex-M4F), prints over semihosting and exits with the comparison's
//! status: `scripts/check_digest_target.sh thumbv7em-none-eabihf`. On a host it
//! is an ordinary program doing the same.

#![cfg_attr(target_os = "none", no_std, no_main)]

use morphiq_numerics_digest::corpus_digest_hex;

const COMMITTED: &str = include_str!("../../reference/determinism.sha256");

/// Whether this target computes the committed digest, with the computed value.
fn check(buffer: &mut [u8; 64]) -> (bool, &str) {
    let computed = corpus_digest_hex(buffer);
    (computed == COMMITTED.trim(), computed)
}

#[cfg(target_os = "none")]
mod bare_metal {
    use semihosting::{println, process};

    #[cortex_m_rt::entry]
    fn main() -> ! {
        let mut buffer = [0; 64];
        let (matches, computed) = super::check(&mut buffer);
        println!("digest {computed}");
        if matches {
            process::exit(0)
        } else {
            println!("expected {}", super::COMMITTED.trim());
            process::exit(1)
        }
    }
}

#[cfg(not(target_os = "none"))]
fn main() -> std::process::ExitCode {
    let mut buffer = [0; 64];
    let (matches, computed) = check(&mut buffer);
    println!("digest {computed}");
    if matches {
        std::process::ExitCode::SUCCESS
    } else {
        eprintln!("expected {}", COMMITTED.trim());
        std::process::ExitCode::FAILURE
    }
}
