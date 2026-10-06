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
    cos, exp, exp2, expm1, ln, ln_1p, log2, log10, sin, sincos, tan,
};
use morphiq_numerics::random::{SplitMix64, Xoshiro256PlusPlus, unit_closed_open, unit_open};
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

    r.0.finalize().into()
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
