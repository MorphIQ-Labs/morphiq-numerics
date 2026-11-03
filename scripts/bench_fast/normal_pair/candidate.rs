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

// Reason: black-box system-libm controls in the unpublished benchmark only.
// Exit condition: none while comparing the platform math calling interface.
#[allow(clippy::disallowed_methods)]
#[inline(always)]
#[unsafe(no_mangle)]
pub extern "C" fn rust_libm_direct(w1: u64, w2: u64) -> Pair {
    let radius = (-2.0 * unit_open(w1).ln()).sqrt();
    let theta = f64::from_bits(0x4019_21fb_5444_2d18)
        * ((w2 >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000));
    let (s, c) = theta.sin_cos();
    Pair {
        x: radius * c,
        y: radius * s,
    }
}

// Reason and exit condition: the same black-box benchmark control as above.
#[allow(clippy::disallowed_methods)]
#[inline(always)]
#[unsafe(no_mangle)]
pub extern "C" fn rust_libm_folded(w1: u64, w2: u64) -> Pair {
    let radius = (-2.0 * unit_open(w1).ln()).sqrt();
    let k = w2 >> 11;
    let octant = k >> 50;
    let j = k & ((1 << 50) - 1);
    let m = if octant & 1 == 0 { j } else { (1 << 50) - j };
    let phi =
        f64::from_bits(0x4019_21fb_5444_2d18) * (m as f64 * f64::from_bits(0x3ca0_0000_0000_0000));
    let (s, c) = phi.sin_cos();
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

fn direct_slice(first: &[u64], second: &[u64], out: &mut [(f64, f64)]) {
    for ((&a, &b), pair) in first.iter().zip(second).zip(out) {
        let p = rust_libm_direct(a, b);
        *pair = (p.x, p.y);
    }
}

fn folded_slice(first: &[u64], second: &[u64], out: &mut [(f64, f64)]) {
    for ((&a, &b), pair) in first.iter().zip(second).zip(out) {
        let p = rust_libm_folded(a, b);
        *pair = (p.x, p.y);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn output_new(n: usize) -> *mut std::ffi::c_void {
    Box::into_raw(Box::new(vec![(0.0_f64, 0.0_f64); n])).cast()
}

/// # Safety
/// `handle` must be a live allocation returned by `output_new`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn output_address(handle: *mut std::ffi::c_void) -> usize {
    let out = unsafe { &*handle.cast::<Vec<(f64, f64)>>() };
    out.as_ptr() as usize
}

/// # Safety
/// `handle` must be returned by `output_new`, unused by other calls, and freed once.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn output_free(handle: *mut std::ffi::c_void) {
    drop(unsafe { Box::from_raw(handle.cast::<Vec<(f64, f64)>>()) });
}

/// Time the public slice or the equivalent reference loop using Rust tuple
/// storage, so the public API is measured without assuming tuple/C layout.
///
/// # Safety
/// Both word pointers must address `n` initialized words for this call.
/// `handle` must be a live `output_new(n)` allocation used exclusively here.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn measure_slice(
    first: *const u64,
    second: *const u64,
    handle: *mut std::ffi::c_void,
    n: usize,
    rounds: u64,
    reference: u8,
) -> u64 {
    let first = unsafe { std::slice::from_raw_parts(first, n) };
    let second = unsafe { std::slice::from_raw_parts(second, n) };
    let out = unsafe { &mut *handle.cast::<Vec<(f64, f64)>>() };
    assert_eq!(out.len(), n);
    let f = match reference {
        0 => morphiq_numerics::fast::random::normal_pair_slice,
        1 => direct_slice,
        2 => folded_slice,
        _ => panic!("unknown slice comparator"),
    };
    let start = std::time::Instant::now();
    for _ in 0..rounds {
        f(first, second, out);
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
