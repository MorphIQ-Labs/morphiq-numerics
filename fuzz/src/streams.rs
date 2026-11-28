//! Seeded streams, unit uniforms and strong and fast normal pairs against the
//! specifications in docs/random.md and docs/fast_random.md. Transcendental
//! values are correctly rounded by black-box MPFR operations.
use morphiq_numerics::fast::random as fast;
use morphiq_numerics::random::{self, SplitMix64, Xoshiro256PlusPlus};
use rug::{Float, float::Constant, float::Round};

/// RN(2 pi), the specification's angle constant.
const TWO_PI: u64 = 0x4019_21fb_5444_2d18;

/// SplitMix64 as docs/random.md states it, in wider integers.
fn split_mix(state: &mut u64) -> u64 {
    const MODULUS: u128 = 1 << 64;
    let reduce = |v: u128| (v % MODULUS) as u64;
    *state = reduce(u128::from(*state) + 0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = reduce(u128::from(z ^ (z >> 30)) * 0xbf58_476d_1ce4_e5b9);
    z = reduce(u128::from(z ^ (z >> 27)) * 0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// One step of xoshiro256++ (A = 17, B = 45, R = 23).
fn xoshiro(s: &mut [u64; 4]) -> u64 {
    let sum = ((u128::from(s[0]) + u128::from(s[3])) % (1 << 64)) as u64;
    let result = ((u128::from(sum.rotate_left(23)) + u128::from(s[0])) % (1 << 64)) as u64;
    let t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = s[3].rotate_left(45);
    result
}

/// `numerator * 2^-53`, exact for numerators below 2^53.
fn unit(numerator: u64) -> f64 {
    let value: Float = Float::with_val(64, numerator) >> 53_u32;
    let result = value.to_f64_round(Round::Nearest);
    assert!(value == result, "inexact uniform");
    result
}

/// The correctly rounded value of `f`, refined until both directions agree.
fn rounded(input: f64, f: fn(&mut Float, Round) -> std::cmp::Ordering) -> f64 {
    for precision in [128, 256, 512, 1024, 2048] {
        let mut low = Float::with_val(precision, input);
        let mut high = low.clone();
        f(&mut low, Round::Down);
        f(&mut high, Round::Up);
        let (a, b) = (
            low.to_f64_round(Round::Nearest),
            high.to_f64_round(Round::Nearest),
        );
        if a.to_bits() == b.to_bits() {
            return a;
        }
    }
    panic!("uniform oracle unresolved at {:016x}", input.to_bits());
}

/// `RN(a * b)`: the 106-bit product is formed exactly, then rounded once.
fn product(a: f64, b: f64) -> f64 {
    let (a, b) = (Float::with_val(53, a), Float::with_val(53, b));
    let (exact, order) = Float::with_val_round(128, &a * &b, Round::Nearest);
    assert_eq!(order, std::cmp::Ordering::Equal, "inexact oracle product");
    exact.to_f64_round(Round::Nearest)
}

/// The documented Box-Muller specification.
fn specified_pair(w1: u64, w2: u64) -> (f64, f64) {
    let u1 = unit(2 * (w1 >> 12) + 1);
    let logarithm = rounded(u1, Float::ln_round);
    let radius = rounded(-2.0 * logarithm, Float::sqrt_round);
    let k = w2 >> 11;
    let (octant, j) = (k >> 50, k % (1 << 50));
    let m = if octant % 2 == 0 { j } else { (1 << 50) - j };
    let phi = product(f64::from_bits(TWO_PI), unit(m));
    let (s, c) = (
        rounded(phi, Float::sin_round),
        rounded(phi, Float::cos_round),
    );
    let (cos, sin) = match octant {
        0 => (c, s),
        1 => (s, c),
        2 => (-s, c),
        3 => (-c, s),
        4 => (-c, -s),
        5 => (-s, -c),
        6 => (s, -c),
        _ => (c, -s),
    };
    (product(radius, cos), product(radius, sin))
}

fn bits((a, b): (f64, f64)) -> [u64; 2] {
    [a.to_bits(), b.to_bits()]
}

fn check_pair(w1: u64, w2: u64) {
    let expected = specified_pair(w1, w2);
    assert_eq!(
        bits(random::normal_pair(w1, w2)),
        bits(expected),
        "normal_pair {w1:016x} {w2:016x}"
    );
    let approximate = fast::normal_pair(w1, w2);
    check_fast_value(approximate.0, expected.0);
    check_fast_value(approximate.1, expected.1);
}

/// docs/fast_random.md: within 2^-38 of the strong output, with its zero sign.
fn check_fast_value(value: f64, strong: f64) {
    assert!(value.is_finite());
    // Both are binary64, so the difference is exact at 2200 bits.
    let value_exact = Float::with_val(53, value);
    let (difference, order) = Float::with_val_round(2200, &value_exact - strong, Round::Nearest);
    assert_eq!(
        order,
        std::cmp::Ordering::Equal,
        "inexact oracle difference"
    );
    let difference = difference.abs();
    assert!(
        difference <= Float::with_val(64, 1) >> 38_u32,
        "fast pair bound {value:e} against {strong:e}"
    );
    if strong == 0.0 {
        assert_eq!(value.to_bits(), strong.to_bits(), "angular zero sign");
    }
}

fn check_uniforms(w: u64) {
    assert_eq!(
        random::unit_closed_open(w).to_bits(),
        unit(w >> 11).to_bits()
    );
    assert_eq!(
        random::unit_open(w).to_bits(),
        unit(2 * (w >> 12) + 1).to_bits()
    );
}

fn check_streams(seed: u64, other: [u64; 4]) {
    let mut library = SplitMix64::new(seed);
    let mut state = seed;
    for _ in 0..8 {
        assert_eq!(library.next_u64(), split_mix(&mut state), "SplitMix64");
    }
    let mut seeding = seed;
    let seeded: [u64; 4] = std::array::from_fn(|_| split_mix(&mut seeding));
    let mut generator = Xoshiro256PlusPlus::new(seed);
    assert_eq!(generator.state(), seeded, "xoshiro seeding");
    let mut reference = seeded;
    for _ in 0..8 {
        assert_eq!(
            generator.next_u64(),
            xoshiro(&mut reference),
            "xoshiro256++"
        );
        assert_eq!(generator.state(), reference);
    }
    let mut pairs = generator.clone();
    let mut words = generator.clone();
    let (a, b) = (words.next_u64(), words.next_u64());
    assert_eq!(
        bits(pairs.next_normal_pair()),
        bits(random::normal_pair(a, b))
    );
    assert_eq!(pairs.state(), words.state());
    let mut split = SplitMix64::new(seed);
    let mut split_words = SplitMix64::new(seed);
    let (a, b) = (split_words.next_u64(), split_words.next_u64());
    assert_eq!(
        bits(split.next_normal_pair()),
        bits(random::normal_pair(a, b))
    );

    assert_eq!(
        Xoshiro256PlusPlus::from_state(other).map(|g| g.state()),
        (other != [0; 4]).then_some(other)
    );
    // A jump is a power of the linear step: it commutes with a step and
    // distributes over the exclusive or of states. The jump distances
    // themselves are checked in crates/reference/tests/random.rs.
    for long in [false, true] {
        let jump = |s: [u64; 4]| match Xoshiro256PlusPlus::from_state(s) {
            Some(mut g) => {
                if long {
                    g.long_jump();
                } else {
                    g.jump();
                }
                g.state()
            }
            None => [0; 4],
        };
        let mut stepped = seeded;
        xoshiro(&mut stepped);
        let mut after = jump(seeded);
        xoshiro(&mut after);
        assert_eq!(jump(stepped), after, "jump does not commute with a step");
        let mixed: [u64; 4] = std::array::from_fn(|i| seeded[i] ^ other[i]);
        let (x, y) = (jump(seeded), jump(other));
        assert_eq!(
            jump(mixed),
            std::array::from_fn(|i| x[i] ^ y[i]),
            "jump is not linear"
        );
    }
}

/// Little-endian words: the first five drive the streams; consecutive pairs,
/// at most 65, drive the normal pairs and their slice.
pub fn check_input(data: &[u8]) {
    let words: Vec<u64> = data
        .as_chunks::<8>()
        .0
        .iter()
        .take(130)
        .map(|w| u64::from_le_bytes(*w))
        .collect();
    if let [seed, a, b, c, d, ..] = words[..] {
        check_streams(seed, [a, b, c, d]);
    }
    let (mut first, mut second) = (Vec::new(), Vec::new());
    for &[w1, w2] in words.as_chunks::<2>().0 {
        check_uniforms(w1);
        check_uniforms(w2);
        check_pair(w1, w2);
        first.push(w1);
        second.push(w2);
    }
    // The fixed angle constant is itself the rounded value of 2 pi.
    assert_eq!(
        (Float::with_val(128, Constant::Pi) * 2_u32).to_f64(),
        f64::from_bits(TWO_PI)
    );
    let mut out = vec![(0.0, 0.0); first.len()];
    fast::normal_pair_slice(&first, &second, &mut out);
    for ((&w1, &w2), &pair) in first.iter().zip(&second).zip(&out) {
        assert_eq!(bits(pair), bits(fast::normal_pair(w1, w2)), "pair slice");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn packet(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    #[test]
    fn word_boundaries_and_octants_satisfy_the_specification() {
        let mut edges = vec![0, 1, u64::MAX, 1 << 63, (1 << 12) - 1, 1 << 12];
        for octant in 0..8_u64 {
            let start = octant << 61;
            edges.extend([start, start.wrapping_sub(1), start + (1 << 11)]);
        }
        for &w1 in &edges {
            for &w2 in &edges {
                check_input(&packet(&[w1, w2]));
            }
        }
        check_input(&packet(&edges));
        check_input(&packet(&[0; 12]));
    }

    #[test]
    fn the_checks_reject_planted_errors() {
        check_fast_value(1.0, 1.0);
        for (value, strong) in [(1.0 + 4.0 / (1_u64 << 39) as f64, 1.0), (0.0, -0.0)] {
            assert!(std::panic::catch_unwind(|| check_fast_value(value, strong)).is_err());
        }
        let (w1, w2) = (12345, 1 << 62);
        let wrong = specified_pair(w1, w2 + (1 << 61));
        assert_ne!(bits(specified_pair(w1, w2)), bits(wrong));
    }

    #[test]
    fn products_are_rounded_once() {
        // z0 here lies near a midpoint: rounding the product to 64 bits and
        // then to 53 gives the neighbouring encoding.
        check_input(include_bytes!("../regressions/streams/double-rounding"));
    }

    #[test]
    fn long_packets_reach_slice_remainders() {
        let mut state = 7;
        for count in [0_usize, 1, 2, 3, 63, 64, 65] {
            let words: Vec<u64> = (0..2 * count).map(|_| split_mix(&mut state)).collect();
            check_input(&packet(&words));
        }
    }
}
