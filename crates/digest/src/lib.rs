//! The determinism digest: one SHA-256 over every public function's output
//! bits on a fixed corpus.
//!
//! The corpus is generated from integers only, so it is the same everywhere,
//! and this crate is `no_std` and allocation-free, so every target computes it:
//! the test hosts, musl, WebAssembly and bare metal alike. A target that
//! computes any output differently produces a different digest. The committed
//! value is `crates/reference/determinism.sha256`; see `docs/determinism.md`.

#![no_std]

use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics::eft::{fast_two_sum, two_prod, two_sum};
use morphiq_numerics::random::{SplitMix64, Xoshiro256PlusPlus, unit_closed_open, unit_open};
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
