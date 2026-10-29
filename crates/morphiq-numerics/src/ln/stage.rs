//! Natural logarithm's reciprocal stage (docs/ln.md): all arithmetic is
//! binary64, in the order transcribed in formal/ln/LnStage.v.

use super::stage_tables::{H, L0, L1, OFF, R, T};
use super::stages::{A_H, K_H, K2_H, decide, reduce};

/// The maximal contiguous block with reciprocal one and zero log words.
/// These endpoints are derived from the generated table, not a fitted cutoff.
const UNIT_CELLS: (u64, u64) = {
    let mut first = R.len();
    let mut end = 0;
    let mut i = 0;
    while i < R.len() {
        if R[i] == 1.0_f64.to_bits() {
            if first == R.len() {
                first = i;
            }
            end = i + 1;
            assert!(T[i].0.to_bits() == 0 && T[i].1.to_bits() == 0);
        }
        i += 1;
    }
    assert!(first < end);
    i = first;
    while i < end {
        assert!(R[i] == 1.0_f64.to_bits());
        i += 1;
    }
    (OFF + ((first as u64) << 43), OFF + ((end as u64) << 43))
};

#[inline(always)]
pub(crate) fn unit_cell(bits: u64) -> bool {
    bits.wrapping_sub(UNIT_CELLS.0) < UNIT_CELLS.1 - UNIT_CELLS.0
}

/// On the unit-reciprocal cells, normalization is the identity and the
/// reduction is exactly x-1 by Sterbenz. Retain the same full polynomial.
#[inline(always)]
pub(crate) fn unit_parts(x: f64) -> (f64, f64, f64, Option<f64>) {
    let z = x - 1.0;
    let (z2, q) = correction(z);
    let eps = z2 * K_H + (z.abs() * K2_H + A_H);
    (z, 0.0 + q, eps, decide(z, 0.0 + q, eps))
}

/// The normalizer supplies `x = 2^e · y`. Return the approximation, its
/// error bound, and the interval test's decision.
#[inline(always)]
pub(crate) fn parts(e: i32, y: f64) -> (f64, f64, f64, Option<f64>) {
    let (re, i, _, z) = reduce(y);
    #[allow(clippy::cast_precision_loss)] // total exponent is in [-1075, 1025]
    let e = (i64::from(e) + re) as f64;
    evaluate(e, i, z)
}

/// The first normalizer already selected this stage's interval. The type
/// carries that invariant; general log-tail inputs keep using `parts`.
#[inline(always)]
pub(crate) fn normalized_parts(reduced: &super::Reduced) -> (f64, f64, f64, Option<f64>) {
    let y = reduced.y();
    let i = reduced.stage_index;
    let r = f64::from_bits(R[i]);
    let z = residual(y, r);
    evaluate(f64::from(reduced.e), i, z)
}

/// The generated reciprocal makes h*rs-1 exactly representable on the
/// reciprocal stage's proved domain. Hardware FMA and the split path agree.
#[inline(always)]
fn residual(h: f64, rs: f64) -> f64 {
    #[cfg(all(
        feature = "std",
        any(
            target_feature = "fma",
            all(target_arch = "aarch64", target_feature = "neon")
        )
    ))]
    {
        // Reason: these targets provide hardware binary64 FMA; no platform
        // libm fallback is possible. Exit: FMA becomes available in core.
        #[allow(clippy::disallowed_methods)]
        h.mul_add(rs, -1.0)
    }
    #[cfg(not(all(
        feature = "std",
        any(
            target_feature = "fma",
            all(target_arch = "aarch64", target_feature = "neon")
        )
    )))]
    {
        let hh = f64::from_bits(h.to_bits() & !0x3ff);
        let hl = h - hh;
        (hh * rs - 1.0) + hl * rs
    }
}

#[inline(always)]
fn evaluate(e: f64, i: usize, z: f64) -> (f64, f64, f64, Option<f64>) {
    let (th, tl) = T[i];
    let ln1 = e * L1 + th;
    let ln0 = e * L0 + tl;
    let (z2, q) = correction(z);
    let s = ln1 + z;
    let e1 = z - (s - ln1);
    let pre = e1 + ln0;
    let lo = pre + q;
    let eps = z2 * K_H + (s.abs() * K2_H + A_H);
    (s, lo, eps, decide(s, lo, eps))
}

#[inline(always)]
fn correction(z: f64) -> (f64, f64) {
    let z2 = z * z;
    let t0 = z * H[0] - 0.5;
    let t1 = z * H[2] + H[1];
    let a1 = z2 * H[3] + t1;
    let p = z2 * a1 + t0;
    let q = z2 * p;
    (z2, q)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_shortcut_selects_exactly_the_reciprocal_one_cells() {
        let width = 1_u64 << 43;
        for cell in 0..512 {
            for offset in [0, 1, 1023, 1024, width / 2, width - 2, width - 1] {
                let bits = OFF + cell * width + offset;
                let x = f64::from_bits(bits);
                let (e, i, r, _) = reduce(x);
                let expected = e == 0 && r == 1.0 && T[i] == (0.0, 0.0);
                assert_eq!(unit_cell(bits), expected, "input {bits:016x}");
                if expected {
                    let a = unit_parts(x);
                    let b = parts(0, x);
                    assert_eq!(
                        (
                            a.0.to_bits(),
                            a.1.to_bits(),
                            a.2.to_bits(),
                            a.3.map(f64::to_bits)
                        ),
                        (
                            b.0.to_bits(),
                            b.1.to_bits(),
                            b.2.to_bits(),
                            b.3.map(f64::to_bits)
                        ),
                        "input {bits:016x}"
                    );
                }
            }
        }
        for x in [
            0.0,
            -0.0,
            -1.0,
            2.0,
            f64::MIN_POSITIVE,
            f64::MAX,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ] {
            assert!(!unit_cell(x.to_bits()));
        }
        let one = unit_parts(1.0);
        assert_eq!((one.0 + one.1).to_bits(), 0);
    }
}
