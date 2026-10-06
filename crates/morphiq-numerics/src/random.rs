//! Seeded integer streams and exact unit uniforms.
//!
//! Every stream is specified bit for bit by integer operations, so a seed
//! produces the same sequence on every target and in any implementation of the
//! same specification. The definitions, their sources and the derivation of
//! the jump polynomials are in
//! [`docs/random.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/random.md).

/// The Weyl increment, the odd integer nearest `2^64/φ` (Steele, Lea and
/// Flood 2014, Figure 16, `GOLDEN_GAMMA`).
const GOLDEN_GAMMA: u64 = 0x9e37_79b9_7f4a_7c15;

/// The SplitMix64 stream: a Weyl sequence with increment `GOLDEN_GAMMA`, each
/// term mixed by Stafford's Mix13.
///
/// Both operations are from Steele, Lea and Flood, "Fast splittable
/// pseudorandom number generators", OOPSLA 2014, Figure 16: the Weyl step is
/// `nextSeed` with `GOLDEN_GAMMA`, and the output mixer is `mix64variant13`.
/// Pairing that mixer with the Weyl sequence is this crate's specification,
/// the variant in common use for seeding (see `docs/random.md`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// The stream starting from `seed`.
    #[must_use]
    #[inline]
    pub const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    /// The next 64-bit word: advance the Weyl sequence, then mix.
    #[inline]
    pub const fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(GOLDEN_GAMMA);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// The xoshiro256++ generator: the xoshiro256 linear engine with the `++`
/// scrambler.
///
/// Blackman and Vigna, "Scrambled linear pseudorandom number generators",
/// ACM TOMS 47(4), 2021 (arXiv:1805.01407v3): Figure 4, with `A = 17` and
/// `B = 45` (Table 2) and `R = 23` (Table 3). Its period is `2^256 - 1`; the
/// all-zero state is excluded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Xoshiro256PlusPlus {
    s: [u64; 4],
}

/// `x^(2^128) mod p`, with `p` the engine's characteristic polynomial; word `i`
/// holds coefficients `64i` to `64i + 63`. From `generators/xoshiro256_jump.py`.
const JUMP: [u64; 4] = [
    0x180e_c6d3_3cfd_0aba,
    0xd5a6_1266_f0c9_392c,
    0xa958_2618_e03f_c9aa,
    0x39ab_dc45_29b1_661c,
];

/// `x^(2^192) mod p`, laid out as [`JUMP`]. From `generators/xoshiro256_jump.py`.
const LONG_JUMP: [u64; 4] = [
    0x76e1_5d3e_fefd_cbbf,
    0xc500_4e44_1c52_2fb3,
    0x7771_0069_854e_e241,
    0x3910_9bb0_2acb_e635,
];

impl Xoshiro256PlusPlus {
    /// The generator whose state is filled by four words of
    /// [`SplitMix64::new(seed)`](SplitMix64::new), as Blackman and Vigna
    /// recommend for a 64-bit seed (§5). The state is never all zero, since
    /// SplitMix64's mixer is a bijection and four consecutive Weyl terms are
    /// distinct.
    #[must_use]
    #[inline]
    pub const fn new(seed: u64) -> Self {
        let mut seeder = SplitMix64::new(seed);
        Self {
            s: [
                seeder.next_u64(),
                seeder.next_u64(),
                seeder.next_u64(),
                seeder.next_u64(),
            ],
        }
    }

    /// The generator with state `s`, or `None` if `s` is all zero.
    #[must_use]
    #[inline]
    pub const fn from_state(s: [u64; 4]) -> Option<Self> {
        if s[0] | s[1] | s[2] | s[3] == 0 {
            None
        } else {
            Some(Self { s })
        }
    }

    /// The current state.
    #[must_use]
    #[inline]
    pub const fn state(&self) -> [u64; 4] {
        self.s
    }

    /// The next 64-bit word: the `++` scrambler on the current state, then one
    /// step of the linear engine (Figure 4).
    #[inline]
    pub const fn next_u64(&mut self) -> u64 {
        let s = &mut self.s;
        let result = s[0].wrapping_add(s[3]).rotate_left(23).wrapping_add(s[0]);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        result
    }

    /// Advance the state by `2^128` steps.
    #[inline]
    pub const fn jump(&mut self) {
        self.apply(&JUMP);
    }

    /// Advance the state by `2^192` steps.
    #[inline]
    pub const fn long_jump(&mut self) {
        self.apply(&LONG_JUMP);
    }

    /// Replace the state `s` by `J(M) s`, where `M` is the engine's transition
    /// and `J` the polynomial with coefficients `polynomial`: the sum of
    /// `M^i s` over the set coefficients `i`, in order of increasing `i`.
    #[inline]
    const fn apply(&mut self, polynomial: &[u64; 4]) {
        let mut sum = [0_u64; 4];
        let mut word = 0;
        while word < 4 {
            let mut bit = 0;
            while bit < 64 {
                if polynomial[word] & (1 << bit) != 0 {
                    sum[0] ^= self.s[0];
                    sum[1] ^= self.s[1];
                    sum[2] ^= self.s[2];
                    sum[3] ^= self.s[3];
                }
                self.next_u64();
                bit += 1;
            }
            word += 1;
        }
        self.s = sum;
    }
}

/// The uniform on `[0, 1)` from a 64-bit word: its top 53 bits `k`, as
/// `k · 2^-53`, exactly (Steele, Lea and Flood 2014, Figure 17, `nextDouble`).
#[must_use]
#[inline]
pub const fn unit_closed_open(word: u64) -> f64 {
    (word >> 11) as f64 * f64::from_bits((1023 - 53) << 52)
}

/// The uniform on `(0, 1)` from a 64-bit word: its top 52 bits `m`, as
/// `(2m + 1) · 2^-53`, exactly.
///
/// The results are the odd multiples of `2^-53` in `(0, 1)`, symmetric about
/// `1/2`. Every value is representable, since `2m + 1 < 2^53`. This mapping is
/// this crate's specification (see `docs/random.md`).
#[must_use]
#[inline]
pub const fn unit_open(word: u64) -> f64 {
    ((word >> 12) * 2 + 1) as f64 * f64::from_bits((1023 - 53) << 52)
}

/// `RN(2π)`.
const TAU: f64 = f64::from_bits(0x4019_21fb_5444_2d18);

/// `(cos θ, sin θ)` for `θ = 2π·k·2^−53`, `0 ≤ k < 2^53`, by octant
/// (`docs/random.md`): `k = o·2^50 + j`, and the angle evaluated is
/// `φ = RN(RN(2π)·m·2^−53)` in `[0, π/4]`, with `m = j` in an even octant and
/// `m = 2^50 − j` in an odd one, measured back from the octant's end. The
/// octant then swaps and negates `cos φ` and `sin φ`, exactly.
fn turn(k: u64) -> (f64, f64) {
    let octant = k >> 50;
    let j = k & ((1 << 50) - 1);
    let m = if octant & 1 == 0 { j } else { (1 << 50) - j };
    #[allow(clippy::cast_precision_loss)] // m <= 2^50
    let (s, c) = crate::trig::sincos(TAU * (m as f64 * f64::from_bits((1023 - 53) << 52)));
    // Octants 1, 2, 5 and 6 swap; 2 to 5 negate the cosine; 4 to 7 the sine.
    let (cos, sin) = if (octant + 1) & 2 != 0 {
        (s, c)
    } else {
        (c, s)
    };
    let cos = if (2..=5).contains(&octant) { -cos } else { cos };
    let sin = if octant >= 4 { -sin } else { sin };
    (cos, sin)
}

/// The Box–Muller pair from two 64-bit words (`docs/random.md`):
///
/// ```text
/// u1 = unit_open(w1),  ρ = sqrt(−2·ln u1)
/// k  = w2 ≫ 11,  (c, s) = (cos θ, sin θ) for θ = 2π·k·2^−53, by octant
/// (RN(ρ·c), RN(ρ·s))
/// ```
///
/// Every step is exact or a correctly rounded function of its inputs ([`ln`],
/// [`sqrt`], [`sincos`] on `[0, π/4]` and binary64 multiplication), so the pair
/// is specified bit for bit. `−2·ln u1` is exact, and `u1 < 1` keeps `ρ > 0`.
///
/// [`ln`]: crate::elementary::ln
/// [`sqrt`]: crate::elementary::sqrt
/// [`sincos`]: crate::elementary::sincos
#[must_use]
pub fn normal_pair(w1: u64, w2: u64) -> (f64, f64) {
    let rho = crate::elementary::sqrt(-2.0 * crate::ln::ln(unit_open(w1)));
    let (c, s) = turn(w2 >> 11);
    (rho * c, rho * s)
}

impl SplitMix64 {
    /// The next Box–Muller pair: [`normal_pair`] of the next two words.
    #[must_use]
    #[inline]
    pub fn next_normal_pair(&mut self) -> (f64, f64) {
        let w1 = self.next_u64();
        normal_pair(w1, self.next_u64())
    }
}

impl Xoshiro256PlusPlus {
    /// The next Box–Muller pair: [`normal_pair`] of the next two words.
    #[must_use]
    #[inline]
    pub fn next_normal_pair(&mut self) -> (f64, f64) {
        let w1 = self.next_u64();
        normal_pair(w1, self.next_u64())
    }
}
