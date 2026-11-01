//! `DoubleWord::exp_split` against independent 600-bit mpmath references
//! (`generators/double_word_exp_reference.py`), decided in exact integer
//! arithmetic.

use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

/// `u² = 2^-106`.
fn u2() -> Exact {
    Exact::power_of_two(-106)
}

/// The published relative bound, `BOUND · u²`, and the reference's own
/// uncertainty, below `2^-150` relative.
const BOUND: i64 = 16;

/// The least integer `c` with `error <= c · u² · reference`, by bisection.
fn units(error: &Exact, reference: &Exact) -> i64 {
    let scale = &u2() * reference;
    let (mut low, mut high) = (0_i64, 1 << 20);
    while low < high {
        let mid = (low + high) / 2;
        if *error <= &Exact::integer(mid) * &scale {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    low
}

#[test]
fn every_reference_case_is_within_the_published_bound() {
    let data: Value =
        serde_json::from_str(include_str!("../fixtures/double_word_exp.json")).unwrap();
    let cases = data["cases"].as_array().unwrap();
    assert!(cases.len() > 20_000, "oracle population");
    let mut worst = 0;
    let mut worst_case = String::new();
    for row in cases {
        let x = DoubleWord::from_parts(word(&row["hi"]), word(&row["lo"])).unwrap();
        let m = row["m"].as_i64().unwrap();
        let reference = &(&Exact::of(word(&row["high"])) + &Exact::of(word(&row["mid"])))
            + &Exact::of(word(&row["low"]));
        let (value, n) = x.exp_split().expect("inside the domain");
        let computed = &(&Exact::of(value.hi()) + &Exact::of(value.lo()))
            * &Exact::power_of_two(i64::from(n) - m);
        let error = (&computed - &reference).abs();
        let c = units(&error, &reference);
        if c > worst {
            worst = c;
            worst_case = format!("{x:?}");
        }
        assert!(
            c <= BOUND,
            "exp_split({x:?}): {c} u² exceeds the published {BOUND} u²"
        );
    }
    println!("worst observed: {worst} u² at {worst_case}");
}
