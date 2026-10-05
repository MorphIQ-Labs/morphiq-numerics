//! The seeded streams against an independent implementation of their papers,
//! and the jump functions against matrix exponentiation of the engine.

use morphiq_numerics::random::{SplitMix64, Xoshiro256PlusPlus, unit_closed_open, unit_open};
use morphiq_numerics_reference::Words;
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/random_streams.json");

fn word(value: &Value) -> u64 {
    u64::from_str_radix(value.as_str().unwrap(), 16).unwrap()
}

#[test]
fn splitmix64_reproduces_the_reference_stream() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let streams = fixture["splitmix64"].as_object().unwrap();
    assert_eq!(streams.len(), 6);
    for (seed, expected) in streams {
        let mut stream = SplitMix64::new(u64::from_str_radix(seed, 16).unwrap());
        for (i, value) in expected.as_array().unwrap().iter().enumerate() {
            assert_eq!(stream.next_u64(), word(value), "seed {seed}, word {i}");
        }
    }
}

#[test]
fn xoshiro256plusplus_reproduces_the_reference_stream() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let streams = fixture["xoshiro256pp"].as_object().unwrap();
    assert_eq!(streams.len(), 6);
    for (seed, expected) in streams {
        let mut stream = Xoshiro256PlusPlus::new(u64::from_str_radix(seed, 16).unwrap());
        for (i, value) in expected.as_array().unwrap().iter().enumerate() {
            assert_eq!(stream.next_u64(), word(value), "seed {seed}, word {i}");
        }
    }
}

/// A 256×256 matrix over GF(2): row `r` is four words, bit `c` of word
/// `c / 64` being entry `(r, c)`. State bit `64w + b` is bit `b` of `s[w]`.
#[derive(Clone)]
struct Matrix(Vec<[u64; 4]>);

impl Matrix {
    /// The engine's transition, column `c` being the next state of the unit
    /// state `e_c`.
    fn transition() -> Self {
        let mut rows = vec![[0_u64; 4]; 256];
        for c in 0..256 {
            let mut unit = [0_u64; 4];
            unit[c / 64] = 1 << (c % 64);
            let mut generator = Xoshiro256PlusPlus::from_state(unit).unwrap();
            generator.next_u64();
            let column = generator.state();
            for (r, row) in rows.iter_mut().enumerate() {
                if column[r / 64] >> (r % 64) & 1 == 1 {
                    row[c / 64] |= 1 << (c % 64);
                }
            }
        }
        Self(rows)
    }

    fn times(&self, other: &Self) -> Self {
        let rows = self
            .0
            .iter()
            .map(|row| {
                let mut out = [0_u64; 4];
                for k in 0..256 {
                    if row[k / 64] >> (k % 64) & 1 == 1 {
                        for (word, other_word) in out.iter_mut().zip(&other.0[k]) {
                            *word ^= other_word;
                        }
                    }
                }
                out
            })
            .collect();
        Self(rows)
    }

    fn apply(&self, s: [u64; 4]) -> [u64; 4] {
        let mut out = [0_u64; 4];
        for (r, row) in self.0.iter().enumerate() {
            let parity = (0..4).map(|w| (row[w] & s[w]).count_ones()).sum::<u32>() & 1;
            out[r / 64] |= u64::from(parity) << (r % 64);
        }
        out
    }
}

fn power_of_two_steps(k: usize) -> Matrix {
    let mut m = Matrix::transition();
    for _ in 0..k {
        m = m.times(&m);
    }
    m
}

#[test]
fn the_transition_matrix_reproduces_one_step() {
    let m = Matrix::transition();
    let mut words = Words::new(0x0bad_5eed_dead_beef);
    for _ in 0..16 {
        let s = [
            words.next_word(),
            words.next_word(),
            words.next_word(),
            words.next_word(),
        ];
        let mut generator = Xoshiro256PlusPlus::from_state(s).unwrap();
        generator.next_u64();
        assert_eq!(m.apply(s), generator.state());
    }
}

#[test]
fn jump_advances_two_to_the_128_steps() {
    let m = power_of_two_steps(128);
    let mut words = Words::new(0x5eed_0000_0000_0128);
    for _ in 0..8 {
        let s = [
            words.next_word(),
            words.next_word(),
            words.next_word(),
            words.next_word(),
        ];
        let mut generator = Xoshiro256PlusPlus::from_state(s).unwrap();
        generator.jump();
        assert_eq!(generator.state(), m.apply(s));
    }
}

#[test]
fn long_jump_advances_two_to_the_192_steps() {
    let m = power_of_two_steps(192);
    let mut words = Words::new(0x5eed_0000_0000_0192);
    for _ in 0..8 {
        let s = [
            words.next_word(),
            words.next_word(),
            words.next_word(),
            words.next_word(),
        ];
        let mut generator = Xoshiro256PlusPlus::from_state(s).unwrap();
        generator.long_jump();
        assert_eq!(generator.state(), m.apply(s));
    }
}

#[test]
fn seeding_never_produces_the_excluded_zero_state() {
    assert!(Xoshiro256PlusPlus::from_state([0; 4]).is_none());
    let mut words = Words::new(0x1);
    for seed in (0..10_000).map(|_| words.next_word()).chain([0, u64::MAX]) {
        assert_ne!(Xoshiro256PlusPlus::new(seed).state(), [0; 4]);
    }
}

#[test]
fn closed_open_uniform_is_the_exact_top_53_bits() {
    let step = f64::from_bits((1023 - 53) << 52);
    assert_eq!(unit_closed_open(0).to_bits(), 0.0_f64.to_bits());
    assert_eq!(unit_closed_open(u64::MAX), 1.0 - step);
    assert_eq!(unit_closed_open(1 << 11), step);
    assert_eq!(unit_closed_open((1 << 11) - 1), 0.0);
    assert_eq!(unit_closed_open(1 << 63), 0.5);
}

#[test]
fn open_uniform_is_symmetric_and_never_an_endpoint() {
    let step = f64::from_bits((1023 - 53) << 52);
    assert_eq!(unit_open(0), step);
    assert_eq!(unit_open(u64::MAX), 1.0 - step);
    let mut words = Words::new(0x00c0_ffee);
    for _ in 0..100_000 {
        let w = words.next_word();
        let u = unit_open(w);
        assert!(u > 0.0 && u < 1.0);
        // The complement word's top 52 bits are 2^52 - 1 - m.
        assert_eq!(unit_open(!w), 1.0 - u, "{w:x}");
    }
}
