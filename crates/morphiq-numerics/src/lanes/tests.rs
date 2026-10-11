//! Every lane kernel returns its scalar function's bits, on every backend this
//! CPU has, each lower backend forced too (docs/lanes.md §6).
//!
//! The corpora: every binary64 in the function's reference fixture (arguments
//! and results alike), every special value and branch edge, random encodings,
//! the argument ranges the batched functions are used on, and slices of every
//! length from 0 to 17. `MORPHIQ_LANE_CASES` scales the random sections
//! (default 2^18 each); `MORPHIQ_REQUIRE_BACKENDS` (comma-separated backend
//! names) fails the run if a listed backend isn't available, so CI states
//! what it exercised.

use std::vec::Vec;

use morphiq_numerics_arch::{Scalar, Simd, WithSimd};

use super::{Kernel, chunks, run, two_prod};
use crate::exp::lanes::Exp;
use crate::internal_crosscheck::reduction_argument;
use crate::ln::lanes::{Ln, Ln1p};
use crate::random::SplitMix64;

/// The random sections' size.
pub(crate) fn cases() -> usize {
    std::env::var("MORPHIQ_LANE_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1 << 18)
}

/// Every binary64 written in a fixture: 16 hex digits between quotes.
fn fixture_values(fixture: &str) -> Vec<f64> {
    fixture
        .split('"')
        .filter(|s| s.len() == 16 && s.bytes().all(|b| b.is_ascii_hexdigit()))
        .map(|s| f64::from_bits(u64::from_str_radix(s, 16).unwrap()))
        .collect()
}

fn unit(rng: &mut SplitMix64) -> f64 {
    #[allow(clippy::cast_precision_loss)] // a 53-bit integer
    let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
    u
}

/// `±m·2^e` with a random significand, `e` in `[low, high]`.
fn binade(rng: &mut SplitMix64, low: i64, high: i64) -> f64 {
    let span = u64::try_from(high - low + 1).unwrap();
    let e = u64::try_from(1023 + low).unwrap() + rng.next_u64() % span;
    let w = rng.next_u64();
    f64::from_bits((w & (1 << 63)) | (e << 52) | (rng.next_u64() >> 12))
}

/// Each value, its neighbours and its negation's.
fn with_neighbours(values: &[f64]) -> Vec<f64> {
    let mut out = Vec::new();
    for &v in values {
        for x in [v, -v] {
            out.push(x);
            if x.is_finite() {
                out.push(f64::from_bits(x.to_bits().wrapping_add(1)));
                out.push(f64::from_bits(x.to_bits().wrapping_sub(1)));
            }
        }
    }
    out
}

/// Special values shared by every corpus.
fn specials() -> Vec<f64> {
    with_neighbours(&[
        0.0,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
        1.0,
        0.5,
        2.0,
        f64::EPSILON,
    ])
}

pub(crate) fn exp_corpus() -> Vec<f64> {
    let mut rng = SplitMix64::new(0x6c61_6e65_5f65_7870);
    let n = cases();
    let mut v = fixture_values(include_str!("../../../reference/fixtures/exp.json"));
    v.extend(specials());
    // Every threshold of docs/exp.md §1, the subnormal-result edge (k = −1021)
    // and the k = 1024 edge, with neighbours.
    v.extend(with_neighbours(&[
        f64::from_bits(0x4086_2e42_fefa_39f0),
        f64::from_bits(0xc087_4910_d52d_3052),
        f64::from_bits(0xbc90_0000_0000_0000),
        f64::from_bits(0x3ca0_0000_0000_0000),
        f64::from_bits(0x3e10_0000_0000_0000),
        -708.396_418_532_264_1,
        -707.7,
        709.43,
        709.089,
    ]));
    for _ in 0..n {
        v.push(f64::from_bits(rng.next_u64()));
        // log_sum_exp's differences, d in [−30, 0].
        v.push(-30.0 * unit(&mut rng));
        // The whole finite domain and past it.
        v.push(-746.0 + 1456.0 * unit(&mut rng));
        // Ties of x/L, tiny arguments.
        v.push(reduction_argument(&mut rng));
        // Every binade near zero, both signs.
        v.push(binade(&mut rng, -60, 0));
        // Near the overflow and subnormal thresholds.
        v.push(709.0 + unit(&mut rng));
        v.push(-746.0 + 40.0 * unit(&mut rng));
    }
    v
}

pub(crate) fn ln_corpus() -> Vec<f64> {
    let mut rng = SplitMix64::new(0x6c61_6e65_5f6c_6e00);
    let n = cases();
    let mut v = fixture_values(include_str!("../../../reference/fixtures/ln.json"));
    v.extend(specials());
    for _ in 0..n {
        v.push(f64::from_bits(rng.next_u64()));
        // Every positive encoding, subnormals included.
        v.push(f64::from_bits(1 + rng.next_u64() % 0x7fef_ffff_ffff_ffff));
        // [0.5, 2), where cancellation is.
        v.push(f64::from_bits(
            0x3fe0_0000_0000_0000 + rng.next_u64() % (1 << 53),
        ));
        // Within 2^-20 of 1.
        v.push(1.0 + (unit(&mut rng) - 0.5) * f64::from_bits(0x3eb0_0000_0000_0000));
        // Subnormals.
        v.push(f64::from_bits(rng.next_u64() % (1 << 52)));
    }
    v
}

pub(crate) fn ln_1p_corpus() -> Vec<f64> {
    let mut rng = SplitMix64::new(0x6c61_6e65_6c6e_3170);
    let n = cases();
    let mut v = fixture_values(include_str!("../../../reference/fixtures/ln.json"));
    v.extend(specials());
    // Each branch edge of docs/ln.md §7, −1 and 2^53, with neighbours.
    v.extend(with_neighbours(&[
        f64::from_bits(0x3c90_0000_0000_0000),
        f64::from_bits(0x3f80_0000_0000_0000),
        f64::from_bits(0x4340_0000_0000_0000),
        -0.5,
    ]));
    for _ in 0..n {
        v.push(f64::from_bits(rng.next_u64()));
        // log_sum_exp's t = e^d, d in [−30, 0].
        v.push(crate::exp::exp(-30.0 * unit(&mut rng)));
        // z²/4, z in [−6, 6].
        let z = 12.0 * unit(&mut rng) - 6.0;
        v.push(z * z / 4.0);
        // [−1, 2^60], magnitudes log-uniform.
        v.push(-1.0 + crate::exp2::exp2(62.0 * unit(&mut rng) - 2.0));
        // Every magnitude from 2^−60 to 2^1023, both signs.
        v.push(binade(&mut rng, -60, 1023));
        // Near −1, around 2^−7 and around 2^53.
        v.push(-1.0 + unit(&mut rng) * f64::from_bits(0x3cb0_0000_0000_0000));
        v.push(binade(&mut rng, -8, -7));
        v.push(binade(&mut rng, 52, 53).abs());
    }
    v
}

/// Runs `G`'s lane kernel on backend `k`, through `k.vectorize` as the
/// library does, and requires the scalar function's bits on every element.
struct Check<'a, G> {
    name: &'a str,
    xs: &'a [f64],
    kernel: core::marker::PhantomData<G>,
}

impl<G: Kernel> WithSimd for Check<'_, G> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut out = std::vec![0.0; self.xs.len()];
        run::<G, K>(k, self.xs, &mut out);
        let mut mismatches = 0_usize;
        for (&x, &y) in self.xs.iter().zip(&out) {
            let want = G::scalar(x);
            if want.to_bits() != y.to_bits() {
                if mismatches < 10 {
                    std::eprintln!(
                        "{} on {}: {x:e} ({:#018x}) gives {y:e}, scalar {want:e}",
                        self.name,
                        K::NAME,
                        x.to_bits()
                    );
                }
                mismatches += 1;
            }
        }
        assert_eq!(mismatches, 0, "{} on {}: mismatches", self.name, K::NAME);
        // Slices of every length from 0 to 17, at every offset into a block,
        // so every remainder and every lane position is exercised.
        for len in 0..=17 {
            for start in 0..8.min(self.xs.len().saturating_sub(len)) {
                let xs = &self.xs[start..start + len];
                let mut out = std::vec![0.0; len];
                run::<G, K>(k, xs, &mut out);
                for (&x, &y) in xs.iter().zip(&out) {
                    assert_eq!(
                        y.to_bits(),
                        G::scalar(x).to_bits(),
                        "{} on {}",
                        self.name,
                        K::NAME
                    );
                }
            }
        }
        std::eprintln!(
            "{} on {}: {} arguments, bit-identical",
            self.name,
            K::NAME,
            self.xs.len()
        );
    }
}

/// A backend this CPU has.
pub(crate) enum Backend {
    Scalar(Scalar),
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    Neon(morphiq_numerics_arch::Neon),
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    Sse2(morphiq_numerics_arch::Sse2),
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    Avx2(morphiq_numerics_arch::Avx2),
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    Avx512(morphiq_numerics_arch::Avx512),
}

/// Every backend this CPU has, the scalar one included; fails if
/// `MORPHIQ_REQUIRE_BACKENDS` lists one that is absent.
pub(crate) fn backends() -> Vec<Backend> {
    // Widest first; the scalar backend last.
    let mut found: Vec<Backend> = std::vec![Backend::Scalar(Scalar::new())];
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        if let Some(s) = Avx512::try_new() {
            found.push(Backend::Avx512(s));
        }
        if let Some(s) = Avx2::try_new() {
            found.push(Backend::Avx2(s));
        }
        found.push(Backend::Sse2(Sse2::new()));
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    found.push(Backend::Neon(morphiq_numerics_arch::Neon::new()));
    found.rotate_left(1);
    let names: Vec<&str> = found.iter().map(Backend::name).collect();
    std::eprintln!("lane backends on this CPU: {names:?}");
    if let Ok(required) = std::env::var("MORPHIQ_REQUIRE_BACKENDS") {
        for want in required.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            assert!(
                names.contains(&want),
                "required backend {want} is not available: {names:?}"
            );
        }
    }
    found
}

impl Backend {
    pub(crate) fn name(&self) -> &'static str {
        match self {
            Backend::Scalar(_) => Scalar::NAME,
            #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
            Backend::Neon(_) => morphiq_numerics_arch::Neon::NAME,
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Sse2(_) => morphiq_numerics_arch::Sse2::NAME,
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Avx2(_) => morphiq_numerics_arch::Avx2::NAME,
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Avx512(_) => morphiq_numerics_arch::Avx512::NAME,
        }
    }

    /// Runs `op` on this backend, inside its feature-enabled wrapper.
    pub(crate) fn vectorize<W: WithSimd<Output = ()>>(&self, op: W) {
        match self {
            Backend::Scalar(s) => s.vectorize(op),
            #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
            Backend::Neon(s) => s.vectorize(op),
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Sse2(s) => s.vectorize(op),
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Avx2(s) => s.vectorize(op),
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Avx512(s) => s.vectorize(op),
        }
    }
}

impl Backend {
    /// `super::chunks` on this backend: `G`'s lanes on the whole chunks at
    /// the start of `xs`; returns how many elements that covered.
    fn chunks<G: Kernel>(&self, xs: &[f64], out: &mut [f64]) -> usize {
        match self {
            Backend::Scalar(s) => chunks::<G, _>(*s, xs, out),
            #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
            Backend::Neon(s) => chunks::<G, _>(*s, xs, out),
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Sse2(s) => chunks::<G, _>(*s, xs, out),
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Avx2(s) => chunks::<G, _>(*s, xs, out),
            #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
            Backend::Avx512(s) => chunks::<G, _>(*s, xs, out),
        }
    }
}

/// Every cascade `map` could run, forced: each subset of this CPU's lane
/// backends, widest first, then the scalar function for what remains. On
/// slices of every length from 0 to 17 at eight offsets, and the whole
/// corpus, every element has the scalar bits (§1).
fn check_cascades<G: Kernel>(name: &str, xs: &[f64]) {
    let lanes: Vec<Backend> = backends()
        .into_iter()
        .filter(|b| !matches!(b, Backend::Scalar(_)))
        .collect();
    let lengths: Vec<(usize, usize)> = (0..=17)
        .flat_map(|len| (0..8).map(move |start| (start, len)))
        .chain([(0, xs.len())])
        .collect();
    for subset in 0..1_u32 << lanes.len() {
        let cascade: Vec<&Backend> = lanes
            .iter()
            .enumerate()
            .filter(|(i, _)| subset >> i & 1 == 1)
            .map(|(_, b)| b)
            .collect();
        let names: Vec<&str> = cascade.iter().map(|b| b.name()).collect();
        for &(start, len) in &lengths {
            let xs = &xs[start..start + len];
            let mut out = std::vec![f64::NAN; len];
            let mut done = 0;
            for backend in &cascade {
                done += backend.chunks::<G>(&xs[done..], &mut out[done..]);
            }
            // What is left is shorter than the narrowest backend's chunk.
            if let Some(narrowest) = cascade.last() {
                assert!(len - done < lanes_of(narrowest), "{names:?}, length {len}");
            }
            for (o, &x) in out[done..].iter_mut().zip(&xs[done..]) {
                *o = G::scalar(x);
            }
            for (&x, &y) in xs.iter().zip(&out) {
                assert_eq!(
                    y.to_bits(),
                    G::scalar(x).to_bits(),
                    "{name}({x:e}) through {names:?}, length {len}"
                );
            }
        }
    }
    std::eprintln!(
        "{name}: every cascade of {:?} bit-identical",
        lanes.iter().map(Backend::name).collect::<Vec<_>>()
    );
}

fn lanes_of(backend: &Backend) -> usize {
    match backend {
        Backend::Scalar(_) => 1,
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        Backend::Neon(_) => 2,
        #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
        Backend::Sse2(_) => 2,
        #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
        Backend::Avx2(_) => 4,
        #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
        Backend::Avx512(_) => 8,
    }
}

#[test]
fn every_lanes_cascade_returns_the_scalar_bits() {
    let short = |v: Vec<f64>| -> Vec<f64> { v.into_iter().step_by(7).take(4_000).collect() };
    check_cascades::<Exp>("exp", &short(exp_corpus()));
    check_cascades::<Ln>("ln", &short(ln_corpus()));
    check_cascades::<Ln1p>("ln_1p", &short(ln_1p_corpus()));
}

fn check_all<G: Kernel>(name: &str, xs: &[f64]) {
    for backend in backends() {
        backend.vectorize(Check::<G> {
            name,
            xs,
            kernel: core::marker::PhantomData,
        });
    }
}

#[test]
fn exp_lanes_return_exps_bits_on_every_backend() {
    check_all::<Exp>("exp", &exp_corpus());
}

#[test]
fn ln_lanes_return_lns_bits_on_every_backend() {
    check_all::<Ln>("ln", &ln_corpus());
}

#[test]
fn ln_1p_lanes_return_ln_1ps_bits_on_every_backend() {
    check_all::<Ln1p>("ln_1p", &ln_1p_corpus());
}

/// The public entry points, on the dispatched backend, for every length up
/// to 17 and a long slice.
#[test]
fn batched_entry_points_return_the_scalar_bits() {
    type Entry = (
        &'static str,
        fn(&[f64], &mut [f64]),
        fn(f64) -> f64,
        Vec<f64>,
    );
    let short = |v: Vec<f64>| -> Vec<f64> { v.into_iter().step_by(7).take(4_000).collect() };
    let entries: [Entry; 3] = [
        (
            "exp_slice",
            crate::elementary::exp_slice,
            crate::exp::exp,
            short(exp_corpus()),
        ),
        (
            "ln_slice",
            crate::elementary::ln_slice,
            crate::ln::ln,
            short(ln_corpus()),
        ),
        (
            "ln_1p_slice",
            crate::elementary::ln_1p_slice,
            crate::ln::ln_1p,
            short(ln_1p_corpus()),
        ),
    ];
    for (name, batched, scalar, xs) in entries {
        for len in (0..=17).chain([xs.len()]) {
            let xs = &xs[..len];
            let mut out = std::vec![f64::NAN; len];
            batched(xs, &mut out);
            for (&x, &y) in xs.iter().zip(&out) {
                assert_eq!(y.to_bits(), scalar(x).to_bits(), "{name}({x:e})");
            }
        }
    }
}

#[test]
#[should_panic(expected = "exp_slice: slices of different lengths")]
fn batched_entry_points_reject_slices_of_different_lengths() {
    crate::elementary::exp_slice(&[1.0, 2.0], &mut [0.0]);
}

/// The lane `two_prod` against `eft::two_prod`, bit for bit: everywhere on a
/// backend without FMA (the same Dekker operations), and on `eft::two_prod`'s
/// domain with FMA (docs/lanes.md §2), zeros of both signs included.
struct TwoProd;

impl WithSimd for TwoProd {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut rng = SplitMix64::new(0x7477_6f5f_7072_6f64);
        let zeros = [0.0, -0.0];
        for round in 0..cases() / K::LANES {
            let (mut a, mut b) = (K::Array::default(), K::Array::default());
            for (x, y) in a.as_mut().iter_mut().zip(b.as_mut()) {
                if K::FMA {
                    // e_a, e_b in [−480, 480]: inside the domain.
                    *x = binade(&mut rng, -480, 480);
                    *y = binade(&mut rng, -480, 480);
                } else {
                    *x = f64::from_bits(rng.next_u64());
                    *y = f64::from_bits(rng.next_u64());
                }
                if round % 16 == 0 {
                    *x = zeros[usize::from(rng.next_u64() & 1 == 1)];
                }
                if round % 16 == 1 {
                    *y = zeros[usize::from(rng.next_u64() & 1 == 1)];
                }
            }
            let (p, e) = two_prod(k, k.load(a), k.load(b));
            let (p, e) = (k.store(p), k.store(e));
            for i in 0..K::LANES {
                let (x, y) = (a.as_ref()[i], b.as_ref()[i]);
                let (wp, we) = crate::eft::two_prod(x, y);
                let same =
                    |u: f64, v: f64| u.to_bits() == v.to_bits() || (u.is_nan() && v.is_nan());
                assert!(
                    same(p.as_ref()[i], wp) && same(e.as_ref()[i], we),
                    "{}: two_prod({x:e}, {y:e})",
                    K::NAME
                );
            }
        }
    }
}

#[test]
fn lane_two_prod_is_efts_two_prod() {
    for backend in backends() {
        backend.vectorize(TwoProd);
    }
}
