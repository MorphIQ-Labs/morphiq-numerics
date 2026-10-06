//! Box–Muller pairs against an independent implementation of the
//! specification (`generators/box_muller_reference.py`, with an interval
//! oracle for `ln`, `sqrt`, `sin` and `cos`), bit for bit: edge words, and the
//! first 256 pairs of each stream from six seeds (docs/random.md).

use morphiq_numerics::random::{SplitMix64, Xoshiro256PlusPlus, normal_pair};
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/box_muller.json");

fn hex(value: &Value) -> u64 {
    u64::from_str_radix(value.as_str().unwrap(), 16).unwrap()
}

fn expected(case: &Value) -> (u64, u64) {
    (hex(&case["z0"]), hex(&case["z1"]))
}

fn bits((z0, z1): (f64, f64)) -> (u64, u64) {
    (z0.to_bits(), z1.to_bits())
}

#[test]
fn normal_pair_matches_the_reference_on_edge_words() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let edges = fixture["edges"].as_array().unwrap();
    assert_eq!(edges.len(), 48);
    for case in edges {
        let (w1, w2) = (hex(&case["w1"]), hex(&case["w2"]));
        assert_eq!(
            bits(normal_pair(w1, w2)),
            expected(case),
            "{w1:016x} {w2:016x}"
        );
    }
}

#[test]
fn both_streams_give_the_reference_pairs() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    for (seed, cases) in fixture["splitmix64"].as_object().unwrap() {
        let mut stream = SplitMix64::new(u64::from_str_radix(seed, 16).unwrap());
        for case in cases.as_array().unwrap() {
            assert_eq!(
                bits(stream.next_normal_pair()),
                expected(case),
                "SplitMix64 {seed}"
            );
        }
    }
    for (seed, cases) in fixture["xoshiro256pp"].as_object().unwrap() {
        let mut stream = Xoshiro256PlusPlus::new(u64::from_str_radix(seed, 16).unwrap());
        for case in cases.as_array().unwrap() {
            assert_eq!(
                bits(stream.next_normal_pair()),
                expected(case),
                "xoshiro256++ {seed}"
            );
        }
    }
}
