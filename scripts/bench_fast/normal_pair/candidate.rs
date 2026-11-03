// Box–Muller screening candidates for #282, outside the published library.
// Coefficients come from prepare.py, independently of any external kernel.
use morphiq_numerics::{fast::elementary::ln, random::unit_open};

include!("coefficients.rs");

#[repr(C)]
pub struct Pair {
    x: f64,
    y: f64,
}

#[inline(always)]
fn polynomial<const N: usize>(x: f64, coefficients: &[f64; N]) -> f64 {
    let mut p = coefficients[N - 1];
    for &c in coefficients[..N - 1].iter().rev() {
        p = c + x * p;
    }
    p
}

#[inline(always)]
fn pair<const N: usize>(w1: u64, w2: u64, sine: &[f64; N], cosine: &[f64; N]) -> Pair {
    let radius = (-2.0 * ln(unit_open(w1))).sqrt();
    let k = w2 >> 11;
    let octant = k >> 50;
    let j = k & ((1 << 50) - 1);
    let m = if octant & 1 == 0 { j } else { (1 << 50) - j };
    let phi =
        f64::from_bits(0x4019_21fb_5444_2d18) * (m as f64 * f64::from_bits(0x3ca0_0000_0000_0000));
    let z = phi * phi;
    let s = phi * polynomial(z, sine);
    let c = polynomial(z, cosine);
    let (c, s) = if (octant + 1) & 2 != 0 {
        (s, c)
    } else {
        (c, s)
    };
    let c = if (2..=5).contains(&octant) { -c } else { c };
    let s = if octant >= 4 { -s } else { s };
    Pair {
        x: radius * c,
        y: radius * s,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn candidate6(w1: u64, w2: u64) -> Pair {
    pair(w1, w2, &SIN6, &COS6)
}

#[unsafe(no_mangle)]
pub extern "C" fn candidate7(w1: u64, w2: u64) -> Pair {
    pair(w1, w2, &SIN7, &COS7)
}

#[unsafe(no_mangle)]
pub extern "C" fn strong(w1: u64, w2: u64) -> Pair {
    let (x, y) = morphiq_numerics::random::normal_pair(w1, w2);
    Pair { x, y }
}
