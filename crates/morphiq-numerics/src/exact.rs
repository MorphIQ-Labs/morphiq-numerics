//! Operations IEEE 754 requires to be correctly rounded, on the hardware where
//! the target has them (`docs/sqrt.md`).
//!
//! A correctly rounded operation returns the same bits wherever it runs, so
//! the hardware instruction and this crate's integer implementation agree
//! exactly, and using the instruction costs the determinism claim nothing.
//! Only the transcendental functions differ between platforms, which is why
//! the crate reaches no `libm`. The integer implementation stays the reference
//! and the fallback for every build without the instruction: without `std`,
//! and on targets whose floating-point unit lacks it.

/// `√x` correctly rounded: the hardware square root on x86-64 (`sqrtsd`),
/// aarch64 (`fsqrt`) and WebAssembly (`f64.sqrt`) when `std` is on, else
/// [`crate::sqrt::sqrt`]; the same bits either way for every `x` but a NaN's
/// payload and sign, which callers never pass (every kernel's argument is
/// finite and nonnegative).
#[inline]
pub(crate) fn sqrt(x: f64) -> f64 {
    #[cfg(all(
        feature = "std",
        any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "wasm32"
        )
    ))]
    {
        // Reason: each of these targets lowers `f64::sqrt` to its binary64
        // square-root instruction, which IEEE 754 §5.4.1 requires to be
        // correctly rounded; it cannot select a platform libm.
        // Exit condition: a correctly rounded square root in `core`, usable
        // without `std`.
        x.sqrt()
    }
    #[cfg(not(all(
        feature = "std",
        any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "wasm32"
        )
    )))]
    {
        crate::sqrt::sqrt(x)
    }
}

#[cfg(test)]
mod tests {
    use crate::random::SplitMix64;

    #[test]
    fn the_square_root_is_the_integer_implementations_on_every_nonnegative_encoding() {
        let mut rng = SplitMix64::new(0x6578_6163_745f_7371);
        let mut values = std::vec![
            0.0,
            f64::from_bits(1),
            f64::MIN_POSITIVE,
            1.0,
            2.0,
            f64::MAX,
            f64::INFINITY
        ];
        for _ in 0..400_000 {
            let w = rng.next_u64() & !(1 << 63);
            values.push(f64::from_bits(w));
            // Every binade's neighbourhood of an exact square.
            values.push(f64::from_bits(
                (w & 0x7fe0_0000_0000_0000) | 0x000f_ffff_ffff_ffff,
            ));
        }
        for x in values {
            let (hardware, software) = (super::sqrt(x), crate::sqrt::sqrt(x));
            assert!(
                hardware.to_bits() == software.to_bits()
                    || (hardware.is_nan() && software.is_nan()),
                "sqrt({x:e}): {hardware:e} against {software:e}"
            );
        }
    }
}
