use super::*;
use crate::test_exact::{entries, word};

/// Discover inputs for the independent generator; the accurate kernel is
/// only a search filter, never the authority for a committed expected value.
#[test]
#[ignore = "development witness search; regenerate selected inputs with mpmath"]
fn normal_find_rounding_witnesses() {
    use crate::random::SplitMix64;
    let mut rng = SplitMix64::new(0x3572_6f75_6e64_696e);
    let mut found = [0; 4];
    for i in 0..(1 << 26) {
        #[allow(clippy::cast_precision_loss)] // 53 bits
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let x = if i % 2 == 0 { u - 0.5 } else { 74.0 * u - 37.0 };
        for (j, op) in [
            Operation::Pdf,
            Operation::Cdf,
            Operation::Centered,
            Operation::LogCdf,
        ]
        .into_iter()
        .enumerate()
        {
            if found[j] >= 16 || special(op, x).is_some() {
                continue;
            }
            let Some((y, eps)) = fast(op, x) else {
                continue;
            };
            let low = y.hi() + (y.lo() - eps);
            let high = y.hi() + (y.lo() + eps);
            if low.to_bits() == high.to_bits() {
                continue;
            }
            let accurate = accurate::evaluate(op, x);
            if y.hi().to_bits() != accurate.to_bits() {
                std::println!(
                    "witness,{op:?},{:016x},{:016x},{:016x}",
                    x.to_bits(),
                    y.hi().to_bits(),
                    accurate.to_bits()
                );
                found[j] += 1;
            }
        }
        if found.iter().all(|&n| n >= 16) {
            break;
        }
    }
    std::println!("witness counts: {found:?}");
}

#[test]
fn extended_erfcx_matches_oracle_across_rounded_lookup_boundaries() {
    use crate::q256::Q256;
    for case in entries(
        include_str!("../../../reference/fixtures/normal.json"),
        &["extended_erfcx"],
    ) {
        let h = word(case, "hi");
        let l = word(case, "lo");
        let x = Q256::from_f64(h).add(Q256::from_f64(l));
        let actual = crate::erfcx::accurate::positive(x).to_f64();
        assert_eq!(
            actual.to_bits(),
            word(case, "erfcx").to_bits(),
            "hi={h:e} lo={l:e}"
        );
    }
}

#[test]
fn normal_compositions_match_independently_rounded_witnesses() {
    for case in entries(
        include_str!("../../../reference/fixtures/normal.json"),
        &["cases"],
    ) {
        let x = word(case, "x");
        let ccdf = evaluate(Operation::Cdf, if x.is_nan() { x } else { -x });
        assert_eq!(
            ccdf.to_bits(),
            word(case, "ccdf").to_bits(),
            "ccdf x={:016x}",
            x.to_bits()
        );
        for (op, name) in [
            (Operation::Pdf, "pdf"),
            (Operation::Cdf, "cdf"),
            (Operation::Centered, "centered"),
            (Operation::LogCdf, "log_cdf"),
        ] {
            let expected = word(case, name);
            let actual = evaluate(op, x);
            assert_eq!(
                actual.to_bits(),
                expected.to_bits(),
                "{op:?} x={:016x} ({x:e}) actual={actual:e} expected={expected:e}",
                x.to_bits()
            );
            if special(op, x).is_none() {
                let actual = accurate::evaluate(op, x);
                assert_eq!(
                    actual.to_bits(),
                    expected.to_bits(),
                    "accurate {op:?} x={:016x} ({x:e}) actual={actual:e} expected={expected:e}",
                    x.to_bits()
                );
            }
        }
    }
}
