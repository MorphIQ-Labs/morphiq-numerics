//! The determinism digest: one SHA-256 over every public function's output
//! bits on a fixed corpus.
//!
//! The corpus is generated from integers only, so it is the same everywhere,
//! and this crate is `no_std` and allocation-free, so every target computes it:
//! the test hosts, musl, WebAssembly and bare metal alike. A target that
//! computes any output differently produces a different digest. The committed
//! value is `crates/reference/determinism.sha256`; see `docs/determinism.md`.

#![no_std]

use morphiq_numerics::double_word::{CheckError, DoubleWord, Hypothesis};
use morphiq_numerics::eft::{fast_two_sum, two_prod, two_sum};
use morphiq_numerics::elementary::{
    asin, asin_slice, asinh, asinh_slice, atan2, atan2_slice, cos, exp, exp_slice, exp2,
    exp2_slice, expm1, expm1_slice, ln, ln_1p, ln_1p_slice, ln_slice, log2, log10, sin, sincos,
    sqrt, tan,
};
use morphiq_numerics::interval::{FiniteInterval, IntervalError};
use morphiq_numerics::linalg::tridiagonal::{DominantTridiagonal, Error as TridiagonalError};
use morphiq_numerics::log_space::{
    NormalizeError, log_diff_exp, log_sum_exp, log_sum_exp_and_normalize, log_sum_exp_pairs,
    normalize_log_weights,
};
use morphiq_numerics::normal::{
    erfcx, erfcx_slice, log_norm_cdf, log_norm_cdf_slice, log_norm_pdf, norm_ccdf, norm_ccdf_slice,
    norm_cdf, norm_cdf_centered, norm_cdf_centered_slice, norm_cdf_slice, norm_pdf, norm_pdf_slice,
};
use morphiq_numerics::random::{
    SplitMix64, Xoshiro256PlusPlus, normal_pair, unit_closed_open, unit_open,
};
use morphiq_numerics::reduce::{dot, dot2, max_abs, sum, sum_squares, sum_squares2, sum2};
use morphiq_numerics::ulp::{ordered_bits, ulp, ulps_between};
use sha2::{Digest, Sha256};

/// A reproducible stream of 64-bit words (xorshift64), so inputs need no
/// platform function and no seed from the environment.
#[derive(Clone, Debug)]
pub struct Words(u64);

impl Words {
    /// A stream from a nonzero seed.
    #[must_use]
    pub const fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// The next word.
    pub fn next_word(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A normal binary64 number with the given exponent (`2^e ≤ |x| < 2^(e+1)`),
    /// a random significand and a random sign.
    ///
    /// # Panics
    ///
    /// If `e` is outside the normal exponent range.
    pub fn with_exponent(&mut self, e: i64) -> f64 {
        assert!((-1022..=1023).contains(&e));
        let word = self.next_word();
        let biased = u64::try_from(e + 1023).unwrap();
        f64::from_bits((word & (1 << 63)) | (biased << 52) | (word >> 12))
    }
}

/// The corpus's output bits, hashed.
struct Recorder(Sha256);

impl Recorder {
    fn f64(&mut self, x: f64) {
        self.0.update(x.to_bits().to_le_bytes());
    }
    fn u64(&mut self, x: u64) {
        self.0.update(x.to_le_bytes());
    }
    fn i64(&mut self, x: i64) {
        self.0.update(x.to_le_bytes());
    }
    fn pair(&mut self, (a, b): (f64, f64)) {
        self.f64(a);
        self.f64(b);
    }
    fn double_word(&mut self, x: DoubleWord) {
        self.pair((x.hi(), x.lo()));
    }
    /// A checked result: its words, or a code for the error.
    fn checked(&mut self, z: Result<DoubleWord, CheckError>) {
        let code = match z {
            Ok(z) => {
                self.double_word(z);
                return;
            }
            Err(CheckError::InvalidOperand) => 1,
            Err(CheckError::DivisionByZero) => 2,
            Err(CheckError::OutsideProvenDomain(Hypothesis::Magnitude)) => 3,
            Err(CheckError::OutsideProvenDomain(Hypothesis::ProductUnderflow)) => 4,
            Err(CheckError::OutsideProvenDomain(Hypothesis::QuotientRange)) => 5,
            Err(CheckError::OutsideProvenDomain(Hypothesis::ZeroResult)) => 6,
            Err(_) => 7,
        };
        self.u64(code);
    }

    /// A section label, so outputs can't shift between functions unnoticed.
    fn label(&mut self, name: &str) {
        self.0.update(name.as_bytes());
    }
}

/// A finite binary64 with exponent in `[low, high]` and a random sign.
fn normal_in(words: &mut Words, low: i64, high: i64) -> f64 {
    let span = u64::try_from(high - low + 1).unwrap();
    let e = low + i64::try_from(words.next_word() % span).unwrap();
    words.with_exponent(e)
}

/// The `ulp` section's inputs in order: the special values, every binade's
/// least and greatest encoding, then random encodings.
fn ulp_inputs(words: &mut Words) -> impl Iterator<Item = f64> + '_ {
    let specials = [
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::MAX,
        f64::MIN,
    ];
    let edges = (0_u64..=2047).flat_map(|e| {
        [
            f64::from_bits(e << 52),
            f64::from_bits((e << 52) | ((1 << 52) - 1)),
        ]
    });
    let random = (0..20_000).map(move |_| f64::from_bits(words.next_word()));
    specials.into_iter().chain(edges).chain(random)
}

/// `sin x`, `cos x` and both halves of `sincos x`.
fn sin_cos(r: &mut Recorder, x: f64) {
    r.f64(sin(x));
    r.f64(cos(x));
    let (s, c) = sincos(x);
    r.f64(s);
    r.f64(c);
}

/// The digest of the whole corpus.
#[must_use]
pub fn corpus_digest() -> [u8; 32] {
    let mut r = Recorder(Sha256::new());
    let mut words = Words::new(0x6d6f_7270_6869_7121);

    r.label("ulp");
    // Each input's ulp and ordered bits, then the steps between neighbours, in
    // two passes over the same reproducible sequence.
    let mut replay = words.clone();
    for x in ulp_inputs(&mut words) {
        r.f64(ulp(x));
        r.i64(ordered_bits(x));
    }
    let mut previous = None;
    for x in ulp_inputs(&mut replay) {
        if let Some(p) = previous {
            r.u64(ulps_between(p, x).unwrap_or(u64::MAX));
        }
        previous = Some(x);
    }

    r.label("eft");
    for _ in 0..20_000 {
        let a = normal_in(&mut words, -500, 500);
        let b = normal_in(&mut words, -500, 500);
        r.pair(two_sum(a, b));
        let (big, small) = if a.abs() >= b.abs() { (a, b) } else { (b, a) };
        r.pair(fast_two_sum(big, small));
        r.pair(two_prod(a, b));
    }

    r.label("double_word");
    for _ in 0..20_000 {
        let x = DoubleWord::sum(
            normal_in(&mut words, -200, 200),
            normal_in(&mut words, -260, -200),
        );
        let y = DoubleWord::sum(
            normal_in(&mut words, -200, 200),
            normal_in(&mut words, -260, -200),
        );
        let f = normal_in(&mut words, -200, 200);
        for z in [
            x.add_f64(f),
            x.add(y),
            x.sub(y),
            x.mul_f64(f),
            x.mul(y),
            x.div_f64(f),
            x.div(y),
        ] {
            r.double_word(z);
        }
        r.double_word(DoubleWord::product(f, x.hi()));
    }

    r.label("double_word_checked");
    // Operands spanning every domain and past it, so each outcome occurs:
    // the result's words, or a code for the reason it was refused.
    for _ in 0..20_000 {
        let mut exponent = || -> i64 {
            let w = words.next_word();
            i64::try_from(w % 2040).unwrap() - 1020
        };
        let (ex, ey, ef) = (exponent(), exponent(), exponent());
        let x = DoubleWord::sum(
            words.with_exponent(ex),
            words.with_exponent((ex - 60).max(-1022)),
        );
        let y = DoubleWord::sum(
            words.with_exponent(ey),
            words.with_exponent((ey - 60).max(-1022)),
        );
        let f = words.with_exponent(ef);
        for z in [
            x.checked_add_f64(f),
            x.checked_add(y),
            x.checked_sub(y),
            x.checked_mul_f64(f),
            x.checked_mul(y),
            x.checked_div_f64(f),
            x.checked_div(y),
            DoubleWord::checked_sum(x.hi(), f),
            DoubleWord::checked_product(x.hi(), f),
        ] {
            r.checked(z);
        }
    }

    r.label("reduce");
    // Slices of every length up to 32 on a fixed stack buffer, with mixed
    // signs and exponents so the sums cancel, plus a NaN for max_abs.
    for len in 0..=32 {
        let mut x = [0.0; 32];
        let mut y = [0.0; 32];
        for (a, b) in x.iter_mut().zip(y.iter_mut()).take(len) {
            *a = normal_in(&mut words, -100, 100);
            *b = normal_in(&mut words, -100, 100);
        }
        let (x, y) = (&x[..len], &y[..len]);
        for v in [
            sum(x),
            sum2(x),
            dot(x, y),
            dot2(x, y),
            sum_squares(x),
            sum_squares2(x),
            max_abs(x),
        ] {
            r.f64(v);
        }
    }
    r.f64(max_abs(&[1.0, f64::NAN, 2.0]));

    r.label("exp");
    // Special values and every boundary of docs/exp.md §1 with its neighbours,
    // then arguments across the whole domain, which reach every path,
    // subnormal results included, and small arguments at every scale.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        1,
        0x7fef_ffff_ffff_ffff,
        0x4086_2e42_fefa_39ef,
        0x4086_2e42_fefa_39f0,
        0xc087_4910_d52d_3052,
        0xc087_4910_d52d_3051,
        0x3ca0_0000_0000_0000,
        0x3c9f_ffff_ffff_ffff,
        0xbc90_0000_0000_0000,
        0xbc90_0000_0000_0001,
    ] {
        r.f64(exp(f64::from_bits(bits)));
    }
    for _ in 0..20_000 {
        // [-746, 710): past both thresholds.
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(exp(-746.0 + 1456.0 * unit));
    }
    for e in -60..0 {
        for _ in 0..64 {
            r.f64(exp(words.with_exponent(e)));
        }
    }

    r.label("ln");
    // Special values, the neighbours of 1, then every positive binade
    // (subnormals included) and arguments near 1, where cancellation is.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0xbff0_0000_0000_0000,
        1,
        0x000f_ffff_ffff_ffff,
        0x7fef_ffff_ffff_ffff,
        0x3ff0_0000_0000_0000,
        0x3ff0_0000_0000_0001,
        0x3fef_ffff_ffff_ffff,
    ] {
        r.f64(ln(f64::from_bits(bits)));
    }
    for _ in 0..20_000 {
        r.f64(ln(f64::from_bits(
            1 + words.next_word() % 0x7fef_ffff_ffff_ffff,
        )));
    }
    for _ in 0..4_000 {
        r.f64(ln(f64::from_bits(
            0x3fe0_0000_0000_0000 + words.next_word() % (1 << 53),
        )));
    }

    r.label("ln_1p");
    // Special values and each branch's edges (docs/ln.md §7), then magnitudes
    // from 2^-60 to 2^1023, either sign where defined.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0xbff0_0000_0000_0000,
        0xbfef_ffff_ffff_ffff,
        0xc000_0000_0000_0000,
        0x3c90_0000_0000_0000,
        0x3c8f_ffff_ffff_ffff,
        0x3f80_0000_0000_0000,
        0xbf80_0000_0000_0000,
        0x4340_0000_0000_0000,
        0x433f_ffff_ffff_ffff,
        0x7fef_ffff_ffff_ffff,
    ] {
        r.f64(ln_1p(f64::from_bits(bits)));
    }
    for _ in 0..20_000 {
        let e = 963 + words.next_word() % 1084;
        let word = words.next_word();
        let x = f64::from_bits((e << 52) | (word >> 12) | (word & (1 << 63)));
        r.f64(ln_1p(x));
    }

    r.label("exp2");
    // Special values, every threshold of docs/exp2.md §1 with its neighbours,
    // integers, then arguments across the whole domain and near zero.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0x408f_ffff_ffff_ffff,
        0x4090_0000_0000_0000,
        0xc090_cbff_ffff_ffff,
        0xc090_cc00_0000_0000,
        0xc08f_f000_0000_0000,
        0xc08f_f000_0000_0001,
        0x3ca7_1547_652b_82fd,
        0x3ca7_1547_652b_82fe,
        0xbc97_1547_652b_82fe,
        0xbc97_1547_652b_82ff,
    ] {
        r.f64(exp2(f64::from_bits(bits)));
    }
    for n in -1076..=1025 {
        r.f64(exp2(f64::from(n)));
    }
    for _ in 0..20_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(exp2(-1077.0 + 2103.0 * unit));
    }
    for e in -60..0 {
        for _ in 0..64 {
            r.f64(exp2(words.with_exponent(e)));
        }
    }

    r.label("expm1");
    // Special values, each threshold of docs/expm1.md §1 with its neighbours,
    // both sides of the 2^-5 switch, then arguments across the whole domain and
    // at every small scale, both signs.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0x4086_2e42_fefa_39ef,
        0x4086_2e42_fefa_39f0,
        0xc042_b708_8723_20e1,
        0xc042_b708_8723_20e2,
        0x3ca6_a09e_667f_3bcc,
        0x3ca6_a09e_667f_3bcd,
        0xbca6_a09e_667f_3bcc,
        0xbca6_a09e_667f_3bcd,
        0x3fa0_0000_0000_0000,
        0x3f9f_ffff_ffff_ffff,
        0xbfa0_0000_0000_0000,
        0xbf9f_ffff_ffff_ffff,
    ] {
        r.f64(expm1(f64::from_bits(bits)));
    }
    for _ in 0..20_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(expm1(-38.0 + 748.0 * unit));
    }
    for e in -60..0 {
        for _ in 0..64 {
            r.f64(expm1(words.with_exponent(e)));
        }
    }

    for (name, f) in [("log2", log2 as fn(f64) -> f64), ("log10", log10)] {
        r.label(name);
        // Special values, 1 and its neighbours, the exact powers, then every
        // positive binade and arguments near 1.
        for bits in [
            0x7ff8_0000_0000_0000,
            0x7ff0_0000_0000_0000,
            0xfff0_0000_0000_0000,
            0,
            1 << 63,
            0xbff0_0000_0000_0000,
            1,
            0x7fef_ffff_ffff_ffff,
            0x3ff0_0000_0000_0000,
            0x3ff0_0000_0000_0001,
            0x3fef_ffff_ffff_ffff,
        ] {
            r.f64(f(f64::from_bits(bits)));
        }
        let mut power = 1.0;
        for _ in 0..=22 {
            r.f64(f(power));
            power *= 10.0;
        }
        for e in -1074..=1023 {
            r.f64(f(f64::from_bits(if e < -1022 {
                1 << (e + 1074)
            } else {
                u64::try_from(e + 1023).unwrap() << 52
            })));
        }
        for _ in 0..20_000 {
            r.f64(f(f64::from_bits(
                1 + words.next_word() % 0x7fef_ffff_ffff_ffff,
            )));
        }
        for _ in 0..4_000 {
            r.f64(f(f64::from_bits(
                0x3fe0_0000_0000_0000 + words.next_word() % (1 << 53),
            )));
        }
    }

    r.label("sin_cos");
    // Special values, each small-argument threshold of docs/sin_cos.md §1 with
    // its neighbour, the binary64 numbers nearest multiples of π/2, the
    // closest approach, then every binade and [-2π, 2π): sin, cos and the
    // pair sincos returns.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0x3e47_1374_4912_3ef6,
        0x3e47_1374_4912_3ef7,
        0x3e46_a09e_667f_3bcc,
        0x3e46_a09e_667f_3bcd,
        0x3e5d_eeea_1168_3f49,
        0x3e5d_eeea_1168_3f4a,
        0x3ff9_21fb_5444_2d18,
        0x4009_21fb_5444_2d18,
        0x7506_ac5b_262c_a1ff,
        0x7fef_ffff_ffff_ffff,
    ] {
        sin_cos(&mut r, f64::from_bits(bits));
    }
    for _ in 0..10_000 {
        let word = words.next_word();
        sin_cos(
            &mut r,
            f64::from_bits((word % 0x7ff0_0000_0000_0000) | (word & (1 << 63))),
        );
    }
    for _ in 0..10_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        sin_cos(&mut r, (2.0 * unit - 1.0) * core::f64::consts::TAU);
    }

    r.label("tan");
    // Special values, docs/sin_cos.md §8's threshold with its neighbour and the
    // edge where tan x = x returns, the binary64 numbers nearest π/2 and π
    // (tan large and near zero), the closest approach, then every binade and
    // [-π, π).
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0x3e4d_12ed_0af1_a27e,
        0x3e4d_12ed_0af1_a27f,
        0x3e50_0000_0000_0000,
        0x3ff9_21fb_5444_2d18,
        0x3ff9_21fb_5444_2d19,
        0x4009_21fb_5444_2d18,
        0x7506_ac5b_262c_a1ff,
        0x7fef_ffff_ffff_ffff,
    ] {
        r.f64(tan(f64::from_bits(bits)));
    }
    for _ in 0..10_000 {
        let word = words.next_word();
        r.f64(tan(f64::from_bits(
            (word % 0x7ff0_0000_0000_0000) | (word & (1 << 63)),
        )));
    }
    for _ in 0..10_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(tan((2.0 * unit - 1.0) * core::f64::consts::PI));
    }

    r.label("asin");
    // Special values, docs/asin.md's thresholds with their neighbours (`asin x = x`
    // below ASIN_IS_X, the complement above SPLIT), ±1 and their neighbours,
    // every shifter edge (k + 1/2)/64 and k/64, then 10,000 arguments in
    // [-1, 1], 5,000 in the complement's range, and the binades near zero.
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        1,
        0x3e57_1374_4912_3ef5,
        0x3e57_1374_4912_3ef6,
        0x3e57_1374_4912_3ef7,
        0x3fe6_a09e_667f_3bcb,
        0x3fe6_a09e_667f_3bcc,
        0x3fe6_a09e_667f_3bcd,
        0x3fef_ffff_ffff_ffff,
        0x3ff0_0000_0000_0000,
        0x3ff0_0000_0000_0001,
        0x7fef_ffff_ffff_ffff,
    ] {
        r.f64(asin(f64::from_bits(bits)));
        r.f64(asin(-f64::from_bits(bits)));
    }
    for k in 0..=64_u32 {
        for numerator in [2 * k, 2 * k + 1] {
            let edge = f64::from(numerator) / 128.0;
            for neighbour in [
                edge,
                f64::from_bits(edge.to_bits() + 1),
                f64::from_bits(edge.to_bits().wrapping_sub(1)),
            ] {
                r.f64(asin(neighbour));
                r.f64(asin(-neighbour));
            }
        }
    }
    for _ in 0..10_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(asin(2.0 * unit - 1.0));
    }
    for _ in 0..5_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(asin(0.7 + 0.3 * unit));
    }
    for exponent in 0..=60_u64 {
        for _ in 0..64 {
            let word = words.next_word();
            r.f64(asin(f64::from_bits(
                (word & (1 << 63)) | ((1023 - exponent) << 52) | (word >> 12),
            )));
        }
    }

    r.label("asinh");
    // Special values, docs/asinh.md's threshold and region edges with their
    // neighbours, the largest finite, then 10,000 arguments over every binade
    // from 2^-30 to 2^1023, both signs, and 5,000 in [-8, 8].
    for bits in [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        1,
        0x3e57_1374_4912_3ef5,
        0x3e57_1374_4912_3ef6,
        0x3e57_1374_4912_3ef7,
        0x3f7f_ffff_ffff_ffff,
        0x3f80_0000_0000_0000,
        0x3f80_0000_0000_0001,
        0x41af_ffff_ffff_ffff,
        0x41b0_0000_0000_0000,
        0x41b0_0000_0000_0001,
        0x7fef_ffff_ffff_ffff,
    ] {
        r.f64(asinh(f64::from_bits(bits)));
        r.f64(asinh(-f64::from_bits(bits)));
    }
    for _ in 0..10_000 {
        let word = words.next_word();
        let biased = 993 + words.next_word() % 1031;
        r.f64(asinh(f64::from_bits(
            (word & (1 << 63)) | (biased << 52) | (word >> 12),
        )));
    }
    for _ in 0..5_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(asinh(16.0 * unit - 8.0));
    }

    r.label("atan2");
    // Every pair of special values, then pairs across the quadrants: ratios in
    // [0, 1] with either argument the larger, the segment boundaries k/64 and
    // their neighbours, equal magnitudes, extreme ratios and random encodings.
    let specials = [
        0x7ff8_0000_0000_0000_u64,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        1,
        0x8000_0000_0000_0001,
        0x3ff0_0000_0000_0000,
        0xbff0_0000_0000_0000,
        0x0010_0000_0000_0000,
        0x7fef_ffff_ffff_ffff,
        0xffef_ffff_ffff_ffff,
    ];
    for y in specials {
        for x in specials {
            r.f64(atan2(f64::from_bits(y), f64::from_bits(x)));
        }
    }
    for _ in 0..10_000 {
        let word = words.next_word();
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let scale = f64::from_bits(((words.next_word() % 800 + 612) << 52) | (word >> 12));
        let (sy, sx) = (
            if word & 1 == 1 { -1.0 } else { 1.0 },
            if word & 2 == 2 { -1.0 } else { 1.0 },
        );
        if word & 4 == 4 {
            r.f64(atan2(sy * unit * scale, sx * scale));
        } else {
            r.f64(atan2(sy * scale, sx * unit * scale));
        }
    }
    for k in 0..=64_u64 {
        let edge = k as f64 / 64.0;
        for step in 0..3_u64 {
            let t = f64::from_bits(edge.to_bits() + step).max(f64::from_bits(1));
            r.f64(atan2(t, 1.0));
            r.f64(atan2(-t, -1.0));
            r.f64(atan2(1.0, t));
            r.f64(atan2(1.0, -t));
        }
    }
    for _ in 0..5_000 {
        let (y, x) = (words.next_word(), words.next_word());
        r.f64(atan2(f64::from_bits(y), f64::from_bits(x)));
    }
    for exponent in 0..1_100_u64 {
        let word = words.next_word();
        let (y, x) = (
            f64::from_bits(((1023 - exponent.min(1022)) << 52) | (word >> 12)),
            1.0 + (word & 0xff) as f64,
        );
        r.f64(atan2(y, x));
        r.f64(atan2(-y, -x));
    }

    r.label("sqrt");
    // Every encoding (both signs, subnormals, infinities and NaNs), then
    // positive arguments in every binade.
    for _ in 0..10_000 {
        r.f64(sqrt(f64::from_bits(words.next_word())));
        r.f64(sqrt(f64::from_bits(
            words.next_word() % 0x7ff0_0000_0000_0000,
        )));
    }

    r.label("normal_pair");
    // Edge words (u1 at its ends and at 1/2; u2 at 0, its greatest value and
    // every octant boundary), then 10,000 pairs of words.
    for w1 in [0, u64::MAX, 1 << 63] {
        for w2 in [0, u64::MAX].into_iter().chain((1..8).map(|o| o << 61)) {
            let (z0, z1) = normal_pair(w1, w2);
            r.f64(z0);
            r.f64(z1);
        }
    }
    for _ in 0..10_000 {
        let (z0, z1) = normal_pair(words.next_word(), words.next_word());
        r.f64(z0);
        r.f64(z1);
    }

    r.label("random");
    for seed in [0, 1, u64::MAX, 0x9e37_79b9_7f4a_7c15] {
        let mut splitmix = SplitMix64::new(seed);
        let mut xoshiro = Xoshiro256PlusPlus::new(seed);
        for _ in 0..4096 {
            let w = splitmix.next_u64();
            r.u64(w);
            r.f64(unit_closed_open(w));
            r.f64(unit_open(w));
            r.u64(xoshiro.next_u64());
        }
        xoshiro.jump();
        r.u64(xoshiro.next_u64());
        xoshiro.long_jump();
        r.u64(xoshiro.next_u64());
    }

    let (inf, nan, max) = (f64::INFINITY, f64::NAN, f64::MAX);
    r.label("log_sum_exp");
    // Special values and zero mass (docs/log_space.md §1), then slices of
    // every length from 1 to 8 whose gaps below their maximum reach
    // cancellation, subnormal and underflowed terms, then pairs across the
    // whole exponent range, past two_sum's domain and into overflow.
    for x in [
        &[][..],
        &[-inf],
        &[-inf, -inf],
        &[nan],
        &[1.0, nan],
        &[inf, 1.0],
        &[-inf, inf],
        &[-0.0],
        &[-inf, -0.0],
        &[-800.0],
        &[0.0, 0.0],
        &[0.0, -745.1],
        &[0.0, -800.0],
        &[max, max],
        &[max, -max],
        &[-max, -max],
    ] {
        r.f64(log_sum_exp(x));
    }
    for len in 1..=8 {
        for _ in 0..1_000 {
            let mut x = [0.0; 8];
            let top = normal_in(&mut words, -8, 10);
            for v in x.iter_mut().take(len) {
                *v = top - normal_in(&mut words, -40, 10).abs();
            }
            r.f64(log_sum_exp(&x[..len]));
        }
    }
    for _ in 0..4_000 {
        let pair = [
            normal_in(&mut words, -1022, 1023),
            normal_in(&mut words, -1022, 1023),
        ];
        r.f64(log_sum_exp(&pair));
    }
    // Longer slices, so the terms cross the chunks whose exponentials the
    // `simd` feature evaluates together (docs/log_space.md decision 7), with
    // zero mass and underflowing terms among them.
    let mut x = [0.0; 100];
    for len in 9..=100 {
        for _ in 0..20 {
            let top = normal_in(&mut words, -8, 10);
            for v in x.iter_mut().take(len) {
                *v = match words.next_word() % 16 {
                    0 => f64::NEG_INFINITY,
                    1 => top - 746.0 - normal_in(&mut words, -8, 8).abs(),
                    _ => top - normal_in(&mut words, -40, 10).abs(),
                };
            }
            r.f64(log_sum_exp(&x[..len]));
        }
    }

    r.label("log_sum_exp_pairs");
    // Every pairing of the special values, then pairs with gaps reaching
    // cancellation and underflow, in batches of 1, 2, 3, 8 and 17.
    let specials = [nan, inf, -inf, 0.0, -0.0, 1.0, -800.0, -745.1, max, -max];
    for a in specials {
        let pairs = specials.map(|b| [a, b]);
        for y in log_sum_exp_pairs(&pairs) {
            r.f64(y);
        }
    }
    for _ in 0..1_000 {
        pairs_section::<1>(&mut r, &mut words);
        pairs_section::<2>(&mut r, &mut words);
        pairs_section::<3>(&mut r, &mut words);
        pairs_section::<8>(&mut r, &mut words);
        pairs_section::<17>(&mut r, &mut words);
    }

    r.label("log_sum_exp_and_normalize");
    // The same pairs as `log_sum_exp_pairs`: every pairing of the special
    // values, then batches of 1, 2, 3, 8 and 17.
    for a in specials {
        normalize_record(&mut r, &specials.map(|b| [a, b]));
    }
    for _ in 0..1_000 {
        normalize_section::<1>(&mut r, &mut words);
        normalize_section::<2>(&mut r, &mut words);
        normalize_section::<3>(&mut r, &mut words);
        normalize_section::<8>(&mut r, &mut words);
        normalize_section::<17>(&mut r, &mut words);
    }

    r.label("log_diff_exp");
    // Special values (§1), then pairs whose gap reaches both regions, the
    // boundary at T and underflow, then pairs across the whole exponent range.
    for (a, b) in [
        (nan, 1.0),
        (1.0, nan),
        (1.0, 2.0),
        (inf, inf),
        (-inf, -inf),
        (3.0, -inf),
        (-0.0, -inf),
        (inf, 5.0),
        (0.0, 0.0),
        (0.0, f64::from_bits(0xbfe6_2e42_fefa_39ef)),
        (0.0, -745.5),
        (max, -max),
    ] {
        r.f64(log_diff_exp(a, b));
    }
    for _ in 0..10_000 {
        let a = normal_in(&mut words, -8, 10);
        r.f64(log_diff_exp(a, a - normal_in(&mut words, -60, 11).abs()));
    }
    for _ in 0..4_000 {
        let (x, y) = (
            normal_in(&mut words, -1022, 1023),
            normal_in(&mut words, -1022, 1023),
        );
        r.f64(log_diff_exp(x.max(y), x.min(y)));
    }

    r.label("log_norm_pdf");
    // Special values, each regime boundary of docs/log_norm_pdf.md §1 with its
    // neighbours, the overflow threshold and a regime-L tie, then arguments
    // across every regime and near zero.
    for bits in [
        0x7ff8_0000_0000_0000_u64, // NaN
        0x7ff0_0000_0000_0000,     // +inf
        0x0000_0000_0000_0000,     // +0
        0x0000_0000_0000_0001,     // least subnormal
        0x3e3f_ffff_ffff_ffff,     // below 2^-27
        0x3e40_0000_0000_0000,     // 2^-27
        0x5f30_0000_0000_0000,     // 2^500
        0x5f30_0000_0000_0001,     // above 2^500
        0x5ff0_0000_0000_0000,     // 2^512
        0x5ff6_a09e_667f_3bcc,     // the overflow threshold, 1.8961503816218352e154
        0x5ff6_a09e_667f_3bcd,     // its successor
        0x6000_0000_0000_0000,     // 2^513
    ] {
        let x = f64::from_bits(bits);
        r.f64(log_norm_pdf(x));
        r.f64(log_norm_pdf(-x));
    }
    r.f64(log_norm_pdf(
        134_217_727.0 * f64::from_bits(0x5dd0_0000_0000_0000),
    )); // a tie: (2^27 - 1)·2^478
    for _ in 0..20_000 {
        r.f64(log_norm_pdf(normal_in(&mut words, -40, 512)));
    }
    for _ in 0..10_000 {
        #[allow(clippy::cast_precision_loss)] // a 53-bit integer
        let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        r.f64(log_norm_pdf(16.0 * unit - 8.0));
    }

    // The batched entry points, on slices of every length up to 17 so every
    // lane count and remainder occurs; with the `simd` feature they run in
    // lanes and must give the same bits.
    r.label("exp_slice");
    let exp_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0x4086_2e42_fefa_39ef,
        0x4086_2e42_fefa_39f0,
        0xc087_4910_d52d_3052,
        0xc087_4910_d52d_3051,
        0x3ca0_0000_0000_0000,
        0x3c9f_ffff_ffff_ffff,
        0xbc90_0000_0000_0000,
        0xbc90_0000_0000_0001,
    ];
    batched_section(&mut r, &mut words, exp_slice, &exp_edges, (-746.0, 710.0));
    r.label("ln_slice");
    let ln_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0,
        1 << 63,
        0xbff0_0000_0000_0000,
        1,
        0x3ff0_0000_0000_0000,
        0x3ff0_0000_0000_0001,
        0x3fef_ffff_ffff_ffff,
    ];
    batched_section(&mut r, &mut words, ln_slice, &ln_edges, (0.0, 4.0));
    r.label("ln_1p_slice");
    let ln_1p_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0,
        1 << 63,
        0xbff0_0000_0000_0000,
        0xbfef_ffff_ffff_ffff,
        0x3c90_0000_0000_0000,
        0x3c8f_ffff_ffff_ffff,
        0x3f80_0000_0000_0000,
        0xbf80_0000_0000_0000,
        0x4340_0000_0000_0000,
        0x433f_ffff_ffff_ffff,
    ];
    batched_section(&mut r, &mut words, ln_1p_slice, &ln_1p_edges, (-1.0, 9.0));

    r.label("asin_slice");
    let asin_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0,
        1 << 63,
        0x3ff0_0000_0000_0000,
        0xbff0_0000_0000_0000,
        0x3e57_1374_4912_3ef6,
        0x3e57_1374_4912_3ef5,
        0x3fe6_a09e_667f_3bcc,
        0x3fe6_a09e_667f_3bcd,
        0x3fef_ffff_ffff_ffff,
    ];
    batched_section(&mut r, &mut words, asin_slice, &asin_edges, (-1.1, 1.1));

    r.label("asinh_slice");
    let asinh_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        0x3e57_1374_4912_3ef6,
        0x3e57_1374_4912_3ef7,
        0x3f80_0000_0000_0000,
        0x41b0_0000_0000_0000,
        0x7fef_ffff_ffff_ffff,
    ];
    batched_section(&mut r, &mut words, asinh_slice, &asinh_edges, (-8.0, 8.0));

    r.label("atan2_slice");
    {
        let (mut y, mut x, mut out) = ([0.0; 17], [0.0; 17], [0.0; 17]);
        let edges = [
            0x7ff8_0000_0000_0000,
            0x7ff0_0000_0000_0000,
            0,
            1 << 63,
            0x3ff0_0000_0000_0000,
            1,
            0x7fef_ffff_ffff_ffff,
        ];
        let mut i = 0;
        for _ in 0..1_000 {
            for len in 1..=17 {
                for j in 0..len {
                    y[j] = batched_input(&mut words, &edges, i, -2.0, 2.0);
                    x[j] = batched_input(&mut words, &edges, i + 1, -2.0, 2.0);
                    i += 3;
                }
                atan2_slice(&y[..len], &x[..len], &mut out[..len]);
                for &v in &out[..len] {
                    r.f64(v);
                }
            }
        }
    }

    r.label("exp2_slice");
    let exp2_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        1,
        (1023 - 55) << 52,
        ((1023 - 55) << 52) - 1,
        1016.0_f64.to_bits(),
        (-1016.0_f64).to_bits(),
        1024.0_f64.to_bits(),
        1024.0_f64.to_bits() - 1,
        (-1075.0_f64).to_bits(),
        (-1075.0_f64).to_bits() - 1,
    ];
    batched_section(
        &mut r,
        &mut words,
        exp2_slice,
        &exp2_edges,
        (-1076.0, 1025.0),
    );
    r.label("expm1_slice");
    let expm1_edges = [
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0,
        1 << 63,
        1,
        0x3c90_0000_0000_0000,
        0x3c8f_ffff_ffff_ffff,
        0x3fa0_0000_0000_0000,
        0x3f9f_ffff_ffff_ffff,
        0xbfa0_0000_0000_0000,
        0xbf9f_ffff_ffff_ffff,
        (-37.0_f64).to_bits(),
        704.0_f64.to_bits(),
        0xc042_b708_8723_20e2,
        0xc042_b708_8723_20e1,
        0x4086_2e42_fefa_39f0,
        0x4086_2e42_fefa_39ef,
    ];
    batched_section(
        &mut r,
        &mut words,
        expm1_slice,
        &expm1_edges,
        (-38.0, 710.0),
    );
    r.label("expm1_slice_small");
    batched_section(
        &mut r,
        &mut words,
        expm1_slice,
        &expm1_edges,
        (-0.03125, 0.03125),
    );

    r.label("erfcx");
    let erfcx_edges = [
        0,
        1 << 63,
        1,
        0x7ff8_0000_0000_1234,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0xc03a_a0f4_d2e0_63cf,
        0xc03a_a0f4_d2e0_63ce,
        0x3c8c_5bf8_91b4_ef6b,
        0x3c8c_5bf8_91b4_ef6c,
        0xbc9c_5bf8_91b4_ef69,
        0xbc9c_5bf8_91b4_ef6a,
        (-0.5_f64).to_bits(),
        1.0_f64.to_bits(),
        16.0_f64.to_bits(),
        512.0_f64.to_bits(),
        1e270_f64.to_bits(),
        0x7fc2_0dd7_5042_9b6d,
        0x7fc2_0dd7_5042_9b6e,
        f64::MAX.to_bits(),
    ];
    for i in 0..20_000 {
        r.f64(erfcx(batched_input(
            &mut words,
            &erfcx_edges,
            i,
            -27.0,
            520.0,
        )));
    }
    r.label("erfcx_slice");
    batched_section(
        &mut r,
        &mut words,
        erfcx_slice,
        &erfcx_edges,
        (-27.0, 520.0),
    );

    interval_section(&mut r, &mut words);
    normal_distribution_section(&mut r, &mut words);

    // Append the new surface after the existing corpus so no older input
    // stream changes. Independent inputs also keep future extension local.
    log_normalization_section(&mut r);
    tridiagonal_section(&mut r);
    tridiagonal_batch_section(&mut r);
    tridiagonal_sign_section(&mut r);

    r.0.finalize().into()
}

fn tridiagonal_error(r: &mut Recorder, error: TridiagonalError) {
    match error {
        TridiagonalError::Shape => r.u64(1),
        TridiagonalError::NonFinite => r.u64(2),
        TridiagonalError::NotDominant(row) => {
            r.u64(3);
            r.u64(u64::try_from(row).unwrap());
        }
        TridiagonalError::ZeroPivot(row) => {
            r.u64(4);
            r.u64(u64::try_from(row).unwrap());
        }
        TridiagonalError::Range => r.u64(5),
        TridiagonalError::NonPositiveDiagonal(row) => {
            r.u64(6);
            r.u64(row as u64);
        }
        TridiagonalError::SameSignLink(link) => {
            r.u64(7);
            r.u64(link as u64);
        }
    }
}

fn tridiagonal_system<const N: usize>(r: &mut Recorder, scale: f64) {
    let mut lower = [0.0; N];
    let mut diagonal = [0.0; N];
    let mut upper = [0.0; N];
    let mut rhs = [0.0; N];
    for i in 0..N {
        let sign = if i % 2 == 0 { 1.0 } else { -1.0 };
        lower[i] = sign * scale;
        diagonal[i] = sign * 4.0 * scale;
        upper[i] = -sign * 0.5 * scale;
    }
    let off = N.saturating_sub(1);
    let a = match DominantTridiagonal::new(&lower[..off], &diagonal, &upper[..off]) {
        Ok(a) => a,
        Err(e) => {
            tridiagonal_error(r, e);
            return;
        }
    };
    r.u64(0);
    r.u64(u64::try_from(a.len()).unwrap());
    r.u64(u64::from(a.is_empty()));
    r.f64(a.dominance_margin());
    let mut pivots = [0.0; N];
    let mut normalized = [0.0; N];
    let f = match a.factor_into(&mut pivots, &mut normalized[..off]) {
        Ok(f) => f,
        Err(e) => {
            tridiagonal_error(r, e);
            return;
        }
    };
    r.u64(0);
    for offset in 0..3 {
        for (i, x) in rhs.iter_mut().enumerate() {
            *x = f64::from(u32::try_from((i + offset) % 7).unwrap()) * scale;
        }
        let mut out = [0.0; N];
        match f.solve_into(&rhs, &mut out) {
            Ok(()) => {
                r.u64(0);
                for x in out {
                    r.f64(x);
                }
                match f.certify(&rhs, &out) {
                    Ok(c) => {
                        r.u64(0);
                        r.f64(c.max_residual());
                        r.f64(c.max_solution_error());
                    }
                    Err(e) => tridiagonal_error(r, e),
                }
            }
            Err(e) => tridiagonal_error(r, e),
        }
    }
}

fn tridiagonal_section(r: &mut Recorder) {
    r.label("linalg::tridiagonal");
    for scale in [
        f64::from_bits(16),
        f64::MIN_POSITIVE,
        0.125,
        1.0,
        1e200,
        f64::MAX,
    ] {
        tridiagonal_system::<0>(r, scale);
        tridiagonal_system::<1>(r, scale);
        tridiagonal_system::<2>(r, scale);
        tridiagonal_system::<3>(r, scale);
        tridiagonal_system::<17>(r, scale);
        tridiagonal_system::<64>(r, scale);
    }
    for d in [0.0, -0.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        tridiagonal_error(r, DominantTridiagonal::new(&[], &[d], &[]).unwrap_err());
    }
    tridiagonal_error(r, DominantTridiagonal::new(&[1.0], &[], &[]).unwrap_err());
    for d in [1.0, 1.0_f64.next_up(), 2.0] {
        match DominantTridiagonal::new(&[1.0, 1.0], &[2.0, d, 2.0], &[1.0, 1.0]) {
            Ok(a) => {
                r.u64(0);
                r.f64(a.dominance_margin());
            }
            Err(e) => tridiagonal_error(r, e),
        }
    }
    let diagonal = [f64::from_bits(1)];
    let a = DominantTridiagonal::new(&[], &diagonal, &[]).unwrap();
    tridiagonal_error(r, a.factor_into(&mut [], &mut []).unwrap_err());
    let mut pivots = [0.0];
    let f = a.factor_into(&mut pivots, &mut []).unwrap();
    for rhs in [f64::NAN, 1.0] {
        tridiagonal_error(r, f.solve_into(&[rhs], &mut [0.0]).unwrap_err());
        tridiagonal_error(r, f.certify(&[rhs], &[0.0]).unwrap_err());
    }
    tridiagonal_error(r, f.solve_into(&[], &mut []).unwrap_err());
    tridiagonal_error(r, f.certify(&[], &[]).unwrap_err());
    let a = DominantTridiagonal::new(&[-f64::MAX / 2.0], &[2.0, f64::MAX], &[1.0]).unwrap();
    tridiagonal_error(r, a.factor_into(&mut [0.0; 2], &mut [0.0]).unwrap_err());
    let a = DominantTridiagonal::new(&[1.0], &[f64::MAX; 2], &[1.0]).unwrap();
    r.f64(a.dominance_margin());
    let mut p = [0.0; 2];
    let mut c = [0.0];
    let f = a.factor_into(&mut p, &mut c).unwrap();
    let mut out = [0.0; 2];
    f.solve_into(&[1.0; 2], &mut out).unwrap();
    for value in out {
        r.f64(value);
    }
    let certificate = f.certify(&[1.0; 2], &out).unwrap();
    r.f64(certificate.max_residual());
    r.f64(certificate.max_solution_error());
}

fn log_normalization_record(r: &mut Recorder, x: &[f64], output: &mut [f64]) {
    match normalize_log_weights(x, output) {
        Ok(value) => {
            r.u64(0);
            r.f64(value.log_sum());
            r.f64(value.max_absolute_error());
        }
        Err(error) => {
            let (code, index) = match error {
                NormalizeError::LengthMismatch => (1, 0),
                NormalizeError::ZeroMass => (2, 0),
                NormalizeError::InvalidWeight(i) => (3, i),
                NormalizeError::TooManyFiniteTerms => (4, 0),
                NormalizeError::Unrepresentable(i) => (5, i),
            };
            r.u64(code);
            r.u64(index as u64);
        }
    }
    for &p in output.iter() {
        r.f64(p);
    }
}

fn log_normalization_section(r: &mut Recorder) {
    r.label("normalize_log_weights");
    let mut out = [42.0; 65];
    for x in [
        &[][..],
        &[f64::NEG_INFINITY],
        &[-0.0],
        &[f64::MAX],
        &[0.0, 0.0, 0.0],
        &[f64::MAX, f64::MAX],
        &[0.0, -800.0, f64::NEG_INFINITY],
        &[0.0, f64::NAN],
        &[f64::INFINITY, 0.0],
        &[-f64::MAX, f64::MAX],
        &[f64::MAX, -f64::MAX],
        &[0.0, f64::from_bits(1), -f64::from_bits(1)],
    ] {
        out.fill(42.0);
        log_normalization_record(r, x, &mut out[..x.len()]);
    }
    log_normalization_record(r, &[0.0], &mut out[..2]);
    let mut words = Words::new(0x6e6f_726d_5f6c_6f67);
    for n in [1, 2, 3, 7, 8, 31, 32, 33, 64, 65] {
        for _ in 0..32 {
            let mut x = [0.0; 65];
            for v in &mut x[..n] {
                *v = match words.next_word() % 16 {
                    0 => f64::NEG_INFINITY,
                    1 => -745.5,
                    _ => normal_in(&mut words, -8, 10),
                };
            }
            out.fill(42.0);
            log_normalization_record(r, &x[..n], &mut out[..n]);
        }
    }
}

/// `N` pairs for the `log_sum_exp_pairs` section: one element of each a
/// random maximum, the other below it by a gap from `2^−40` to `2^11`, either
/// first.
fn pairs_section<const N: usize>(r: &mut Recorder, words: &mut Words) {
    let mut pairs = [[0.0; 2]; N];
    for pair in &mut pairs {
        let top = normal_in(words, -8, 10);
        let other = top - normal_in(words, -40, 10).abs();
        *pair = if words.next_word() & 1 == 0 {
            [top, other]
        } else {
            [other, top]
        };
    }
    for y in log_sum_exp_pairs(&pairs) {
        r.f64(y);
    }
}

/// `N` random pairs as `pairs_section` draws them, through
/// `log_sum_exp_and_normalize`.
fn normalize_section<const N: usize>(r: &mut Recorder, words: &mut Words) {
    let mut pairs = [[0.0; 2]; N];
    for pair in &mut pairs {
        let top = normal_in(words, -8, 10);
        let other = top - normal_in(words, -40, 10).abs();
        *pair = if words.next_word() & 1 == 0 {
            [top, other]
        } else {
            [other, top]
        };
    }
    normalize_record(r, &pairs);
}

/// Each pair's log-sum and normalized pair. A normalized pair that is absent
/// records a code; a NaN entry, whose payload is unspecified, records one too.
fn normalize_record<const N: usize>(r: &mut Recorder, pairs: &[[f64; 2]; N]) {
    for (y, p) in log_sum_exp_and_normalize(pairs) {
        r.f64(y);
        match p {
            None => r.u64(1),
            Some(p) => {
                for v in p {
                    if v.is_nan() {
                        r.u64(2);
                    } else {
                        r.f64(v);
                    }
                }
            }
        }
    }
}

/// The batched sections' inputs: special values and branch edges, random
/// encodings, and arguments across `low..high`, in turn.
fn batched_input(words: &mut Words, edges: &[u64], i: usize, low: f64, high: f64) -> f64 {
    match i % 4 {
        0 => f64::from_bits(edges[(i / 4) % edges.len()]),
        1 => f64::from_bits(words.next_word()),
        _ => {
            #[allow(clippy::cast_precision_loss)] // a 53-bit integer
            let unit = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
            low + (high - low) * unit
        }
    }
}

/// One batched function on 1,000 slices of each length from 1 to 17: every
/// output of `batched`, in order.
fn batched_section(
    r: &mut Recorder,
    words: &mut Words,
    batched: fn(&[f64], &mut [f64]),
    edges: &[u64],
    (low, high): (f64, f64),
) {
    let (mut x, mut out) = ([0.0; 17], [0.0; 17]);
    let mut i = 0;
    for _ in 0..1_000 {
        for len in 1..=17 {
            for v in &mut x[..len] {
                *v = batched_input(words, edges, i, low, high);
                i += 1;
            }
            batched(&x[..len], &mut out[..len]);
            for &y in &out[..len] {
                r.f64(y);
            }
        }
    }
}

/// The digest as lowercase hex, written into `out`.
#[must_use]
pub fn corpus_digest_hex(out: &mut [u8; 64]) -> &str {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for (i, byte) in corpus_digest().iter().enumerate() {
        out[2 * i] = HEX[usize::from(byte >> 4)];
        out[2 * i + 1] = HEX[usize::from(byte & 0xf)];
    }
    core::str::from_utf8(out).expect("hex digits are ASCII")
}

/// Every finite-interval operation, including typed errors and zero signs.
fn interval_section(r: &mut Recorder, words: &mut Words) {
    r.label("finite_interval");
    let edges = [
        0.0,
        -0.0,
        f64::from_bits(1),
        -f64::from_bits(1),
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        f64::MAX,
        -f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        1.0,
        -1.0,
        0.5,
        -1000.0,
        710.0,
    ];
    for i in 0..4096 {
        let a = if i < edges.len() * edges.len() {
            edges[i % edges.len()]
        } else {
            f64::from_bits(words.next_word())
        };
        let b = if i < edges.len() * edges.len() {
            edges[i / edges.len()]
        } else {
            f64::from_bits(words.next_word())
        };
        record_interval(r, FiniteInterval::point(a));
        record_interval(r, FiniteInterval::new(a, b));
        if let (Ok(x), Ok(y)) = (
            FiniteInterval::new(if a <= b { a } else { b }, if a <= b { b } else { a }),
            FiniteInterval::new(
                if b <= 1.0 { b } else { 1.0 },
                if b <= 1.0 { 1.0 } else { b },
            ),
        ) {
            for probe in [a, b, 0.0, f64::NAN, f64::INFINITY] {
                r.u64(u64::from(x.contains(probe)));
            }
            for value in [
                Ok(x.negated()),
                Ok(x.abs()),
                Ok(x.max(y)),
                x.checked_add(y),
                x.checked_sub(y),
                x.checked_mul(y),
                x.checked_div(y),
                x.checked_square(),
                x.checked_ln(),
                x.checked_exp(),
                x.checked_sqrt(),
            ] {
                record_interval(r, value);
            }
        }
    }
}

fn record_interval(r: &mut Recorder, value: Result<FiniteInterval, IntervalError>) {
    match value {
        Ok(x) => {
            r.u64(0);
            r.f64(x.lower());
            r.f64(x.upper());
        }
        Err(IntervalError::InvalidBounds) => r.u64(1),
        Err(IntervalError::Domain) => r.u64(2),
        Err(IntervalError::Range) => r.u64(3),
    }
}

/// Scalar and slice normal-family outputs, with threshold neighbors,
/// signed special values, every short-vector remainder and random encodings.
fn normal_distribution_section(r: &mut Recorder, words: &mut Words) {
    let edges = [
        0_u64,
        1 << 63,
        1,
        (1 << 63) | 1,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff8_1234_5678_9abc,
        0xfff8_1234_5678_9abc,
        0x23d0_0000_0000_0000,
        0x3de0_0000_0000_0000,
        0x3fe0_0000_0000_0000,
        0x4020_95b0_59d6_7c4d,
        0x4020_bfaf_e7a9_1e68,
        0x4036_a09e_667f_3bcd,
        0x4042_8000_0000_0000,
        0x4043_3e21_dc3f_3bd8,
        0x4043_4a42_9ac2_a6bc,
        0x5ff6_a09e_667f_3bcd,
    ];
    type Scalar = fn(f64) -> f64;
    type Slice = fn(&[f64], &mut [f64]);
    for (name, scalar, slice) in [
        ("norm_pdf", norm_pdf as Scalar, norm_pdf_slice as Slice),
        ("norm_cdf", norm_cdf, norm_cdf_slice),
        ("norm_ccdf", norm_ccdf, norm_ccdf_slice),
        (
            "norm_cdf_centered",
            norm_cdf_centered,
            norm_cdf_centered_slice,
        ),
        ("log_norm_cdf", log_norm_cdf, log_norm_cdf_slice),
    ] {
        r.label(name);
        for &bits in &edges {
            for sign in [0, 1 << 63] {
                for neighbor in [bits.saturating_sub(1), bits, bits.saturating_add(1)] {
                    r.f64(scalar(f64::from_bits(neighbor ^ sign)));
                }
            }
        }
        for i in 0..512 {
            r.f64(scalar(batched_input(words, &edges, i, -40.0, 40.0)));
        }
        r.label("slice");
        for len in 0..=17 {
            for sample in 0..8 {
                let mut input = [0.0; 17];
                let mut output = [0.0; 17];
                for (i, x) in input[..len].iter_mut().enumerate() {
                    *x = batched_input(words, &edges, sample * 17 + i, -40.0, 40.0);
                }
                slice(&input[..len], &mut output[..len]);
                for &y in &output[..len] {
                    r.f64(y);
                }
            }
        }
    }
}

fn tridiagonal_batch_section(r: &mut Recorder) {
    r.label("linalg::tridiagonal::solve_many_into");
    for scale in [1.0, -1.0, f64::MIN_POSITIVE / 16.0, 1e270] {
        let lower = [-scale; 16];
        let diagonal = [4.0 * scale; 17];
        let upper = [0.5 * scale; 16];
        for n in [0_usize, 1, 2, 3, 17] {
            let a = DominantTridiagonal::new(
                &lower[..n.saturating_sub(1)],
                &diagonal[..n],
                &upper[..n.saturating_sub(1)],
            )
            .unwrap();
            let mut p = [0.0; 17];
            let mut c = [0.0; 16];
            let f = a
                .factor_into(&mut p[..n], &mut c[..n.saturating_sub(1)])
                .unwrap();
            let mut rhs = [0.0; 17 * 17];
            let mut out = [0.0; 17 * 17];
            for count in [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17] {
                for (i, x) in rhs[..n * count].iter_mut().enumerate() {
                    *x = f64::from(i32::try_from((i * 7) % 19).unwrap() - 9) * scale;
                }
                f.solve_many_into(count, &rhs[..n * count], &mut out[..n * count])
                    .unwrap();
                for &x in &out[..n * count] {
                    r.f64(x);
                }
            }
            if n > 0 {
                tridiagonal_error(r, f.solve_many_into(1, &rhs[..n], &mut []).unwrap_err());
                tridiagonal_error(r, f.solve_many_into(usize::MAX, &[], &mut []).unwrap_err());
                rhs[n * 9 - 1] = f64::NAN;
                tridiagonal_error(
                    r,
                    f.solve_many_into(9, &rhs[..n * 9], &mut out[..n * 9])
                        .unwrap_err(),
                );
            }
        }
    }
    let mut pivots = [0.0];
    let diagonal = [f64::from_bits(1)];
    let f = DominantTridiagonal::new(&[], &diagonal, &[])
        .unwrap()
        .factor_into(&mut pivots, &mut [])
        .unwrap();
    for column in 0..9 {
        let mut rhs = [0.0; 9];
        rhs[column] = 1.0;
        tridiagonal_error(r, f.solve_many_into(9, &rhs, &mut [0.0; 9]).unwrap_err());
    }
}

fn tridiagonal_sign_section(r: &mut Recorder) {
    use morphiq_numerics::linalg::tridiagonal::SignTridiagonal;
    r.label("linalg::tridiagonal::sign_domain");
    for scale in [f64::from_bits(16), f64::MIN_POSITIVE, 1.0, 1e270] {
        for n in [0_usize, 1, 2, 3, 17] {
            let lower = [-2.0 * scale; 16];
            let upper = [scale; 16];
            let mut diagonal = [scale; 17];
            diagonal[0] = 2.0 * scale;
            let mut p = [0.0; 17];
            let mut c = [0.0; 16];
            let off = n.saturating_sub(1);
            let f = SignTridiagonal::new(&lower[..off], &diagonal[..n], &upper[..off])
                .unwrap()
                .factor_into(&mut p[..n], &mut c[..off])
                .unwrap();
            for count in [0, 1, 2, 3, 4, 7, 8, 9, 17] {
                let mut rhs = [0.0; 289];
                let mut out = [0.0; 289];
                for (i, v) in rhs[..n * count].iter_mut().enumerate() {
                    *v = f64::from(i32::try_from(i % 13).unwrap() - 6) * scale;
                }
                f.solve_many_into(count, &rhs[..n * count], &mut out[..n * count])
                    .unwrap();
                for &v in &out[..n * count] {
                    r.f64(v);
                }
                if count > 0 {
                    let mut b = [0.0; 17];
                    let mut x = [0.0; 17];
                    for i in 0..n {
                        b[i] = rhs[i * count];
                        x[i] = out[i * count];
                    }
                    match f.certify_residual(&b[..n], &x[..n]) {
                        Ok(c) => r.f64(c.max_residual()),
                        Err(e) => tridiagonal_error(r, e),
                    }
                }
            }
        }
    }
    for d in [0.0, -0.0, -1.0, f64::NAN] {
        tridiagonal_error(r, SignTridiagonal::new(&[], &[d], &[]).unwrap_err());
    }
    for link in [f64::from_bits(1), -f64::from_bits(1), f64::MAX] {
        tridiagonal_error(
            r,
            SignTridiagonal::new(&[link], &[1.0; 2], &[link]).unwrap_err(),
        );
    }
    for (l, u) in [(0.0, -1.0), (-0.0, 1.0), (-1.0, -0.0), (1.0, 0.0)] {
        let mut p = [0.0; 2];
        let mut c = [0.0];
        let lower = [l];
        let upper = [u];
        let f = SignTridiagonal::new(&lower, &[1.0; 2], &upper)
            .unwrap()
            .factor_into(&mut p, &mut c)
            .unwrap();
        let mut out = [0.0; 2];
        f.solve_into(&[-0.0, 0.0], &mut out).unwrap();
        for v in out {
            r.f64(v);
        }
    }
}
