//! The determinism digest: one SHA-256 over every public function's output
//! bits on a fixed corpus.
//!
//! The corpus is generated from integers only, so it is the same everywhere.
//! A target that computes any output differently produces a different digest.
//! The committed value is `crates/reference/determinism.sha256`; changing it
//! is a deliberate act, recorded with its reason in the pull request.

use crate::Words;
use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics::eft::{fast_two_sum, two_prod, two_sum};
use morphiq_numerics::random::{SplitMix64, Xoshiro256PlusPlus, unit_closed_open, unit_open};
use morphiq_numerics::ulp::{ordered_bits, ulp, ulps_between};
use sha2::{Digest, Sha256};

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

/// The digest of the whole corpus, as lowercase hex.
#[must_use]
pub fn corpus_digest() -> String {
    let mut r = Recorder(Sha256::new());
    let mut words = Words::new(0x6d6f_7270_6869_7121);

    r.label("ulp");
    let mut specials = vec![
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::MAX,
        f64::MIN,
    ];
    specials.extend((0_u64..=2047).flat_map(|e| {
        [
            f64::from_bits(e << 52),
            f64::from_bits((e << 52) | ((1 << 52) - 1)),
        ]
    }));
    specials.extend((0..20_000).map(|_| f64::from_bits(words.next_word())));
    for &x in &specials {
        r.f64(ulp(x));
        r.i64(ordered_bits(x));
    }
    for pair in specials.windows(2) {
        r.u64(ulps_between(pair[0], pair[1]).unwrap_or(u64::MAX));
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

    r.0.finalize().iter().map(|b| format!("{b:02x}")).collect()
}
