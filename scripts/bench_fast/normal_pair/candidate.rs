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
pub extern "C" fn product(w1: u64, w2: u64) -> Pair {
    let (x, y) = morphiq_numerics::fast::random::normal_pair(w1, w2);
    Pair { x, y }
}

/// Time the public slice or the equivalent reference loop using Rust tuple
/// storage, so the public API is measured without assuming tuple/C layout.
///
/// # Safety
/// Both pointers must address `n` initialized words for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn measure_slice(
    first: *const u64,
    second: *const u64,
    n: usize,
    rounds: u64,
    reference: Option<extern "C" fn(u64, u64) -> Pair>,
) -> u64 {
    let first = unsafe { std::slice::from_raw_parts(first, n) };
    let second = unsafe { std::slice::from_raw_parts(second, n) };
    let mut out = vec![(0.0, 0.0); n];
    let start = std::time::Instant::now();
    for _ in 0..rounds {
        if let Some(f) = reference {
            for ((&a, &b), pair) in first.iter().zip(second).zip(&mut out) {
                let p = f(a, b);
                *pair = (p.x, p.y);
            }
        } else {
            morphiq_numerics::fast::random::normal_pair_slice(first, second, &mut out);
        }
        std::hint::black_box(&out);
    }
    start.elapsed().as_nanos() as u64
}

/// Xoshiro256++ plus a normal pair; optionally consume the cached normals
/// in two antithetic updates. The same generator and seed serve each control.
#[unsafe(no_mangle)]
pub extern "C" fn measure_stream(
    f: extern "C" fn(u64, u64) -> Pair,
    count: u64,
    antithetic: bool,
) -> u64 {
    let mut rng = morphiq_numerics::random::Xoshiro256PlusPlus::new(282);
    let (mut plus, mut minus) = (0.0, 0.0);
    let start = std::time::Instant::now();
    for _ in 0..count {
        let pair = f(rng.next_u64(), rng.next_u64());
        if antithetic {
            for z in [pair.x, pair.y] {
                plus += z;
                minus -= z;
            }
        } else {
            std::hint::black_box((pair.x, pair.y));
        }
    }
    std::hint::black_box((plus, minus));
    start.elapsed().as_nanos() as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn strong(w1: u64, w2: u64) -> Pair {
    let (x, y) = morphiq_numerics::random::normal_pair(w1, w2);
    Pair { x, y }
}
