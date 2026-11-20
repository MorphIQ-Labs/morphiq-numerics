//! Compare intermediate words and acceptance decisions on every available
//! backend, before the public scalar fallback could conceal a lane mismatch.
use morphiq_numerics_arch::{Simd, WithSimd};

use super::fast_value;
use crate::lanes::decide_relative;
use crate::lanes::tests::{backends, radix_log_corpus};
use crate::ln::Reduced;

struct Values<'a, const BASE10: bool>(&'a [f64]);

impl<const BASE10: bool> WithSimd for Values<'_, BASE10> {
    type Output = ();

    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0;
        let mut accepted = 0;
        let mut rejected = 0;
        let mut screened = 0;
        for chunk in self.0.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let (value, active) = fast_value::<K, BASE10>(k, x);
            let decision = decide_relative(k, value, crate::ln::EPS) & active;
            let (hi, lo) = (k.store(value.0), k.store(value.1));
            for (lane, &input) in chunk.iter().enumerate() {
                let ordinary = super::super::special(input).is_none();
                assert_eq!(active >> lane & 1 != 0, ordinary);
                if !ordinary {
                    screened += 1;
                    continue;
                }
                let reduced = Reduced::of(input);
                let expected = if BASE10 {
                    super::super::log10_fast(&reduced)
                } else {
                    super::super::log2_fast(&reduced)
                };
                assert_eq!(
                    (hi.as_ref()[lane].to_bits(), lo.as_ref()[lane].to_bits()),
                    (expected.hi().to_bits(), expected.lo().to_bits()),
                    "base10={BASE10}, input={:016x}, backend={}",
                    input.to_bits(),
                    K::NAME
                );
                let scalar_decision = crate::ln::decide(expected);
                assert_eq!(decision >> lane & 1 != 0, scalar_decision.is_some());
                if let Some(result) = scalar_decision {
                    assert_eq!(hi.as_ref()[lane].to_bits(), result.to_bits());
                    accepted += 1;
                } else {
                    rejected += 1;
                }
                compared += 1;
            }
        }
        assert!(compared > self.0.len() / 3);
        assert!(accepted > 0 && rejected > 0 && screened > 0);
        std::eprintln!(
            "{} base10={BASE10}: {compared} compared, {accepted} accepted, {rejected} rejected, {screened} screened",
            K::NAME
        );
    }
}

#[test]
fn radix_log_lanes_match_scalar_intermediates_and_decisions() {
    let xs = radix_log_corpus();
    for backend in backends() {
        backend.vectorize(Values::<false>(&xs));
        backend.vectorize(Values::<true>(&xs));
    }
}

fn decided_by<const BASE10: bool>(x: f64) -> (&'static str, f64) {
    if let Some(value) = super::super::special(x) {
        return ("screen", value);
    }
    let reduced = Reduced::of(x);
    let fast = if BASE10 {
        super::super::log10_fast(&reduced)
    } else {
        super::super::log2_fast(&reduced)
    };
    if let Some(value) = crate::ln::decide(fast) {
        return ("fast", value);
    }
    let accurate = if BASE10 {
        super::super::log10_accurate(&reduced)
    } else {
        super::super::log2_accurate(&reduced)
    };
    ("accurate", accurate.to_f64())
}

#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn native_performance_radix_log() {
    use crate::lanes::tests::bench::{Draw, function};
    static SCREENED: [f64; 7] = [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        -1.0,
        0.0,
        -0.0,
        1.0,
    ];
    static BOUNDARIES: [f64; 8] = [
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        0.5,
        f64::from_bits(0x3fef_ffff_ffff_ffff),
        f64::from_bits(0x3ff0_0000_0000_0001),
        2.0,
        10.0,
        f64::MAX,
    ];
    static POSITIVE: Draw = Draw::Bits(1, 0x7fef_ffff_ffff_ffff);
    static CLOSE: Draw = Draw::Uniform(
        1.0 - 1.0 / 281_474_976_710_656.0,
        1.0 / 140_737_488_355_328.0,
    );
    static MIXED: [Draw; 4] = [
        Draw::Uniform(0.5, 1.5),
        POSITIVE,
        Draw::Values(&SCREENED),
        Draw::Bits(1, 0x000f_ffff_ffff_ffff),
    ];
    let workloads = [
        ("common", Draw::Uniform(0.5, 1.5)),
        ("positive", POSITIVE),
        ("close_to_one", CLOSE),
        ("subnormal", Draw::Bits(1, 0x000f_ffff_ffff_ffff)),
        ("boundaries", Draw::Values(&BOUNDARIES)),
        ("screened", Draw::Values(&SCREENED)),
        ("mixed", Draw::Mixed(&MIXED)),
        ("fallback", Draw::Fallback(&POSITIVE)),
    ];
    function::<super::Radix<false>>("log2", decided_by::<false>, &workloads);
    function::<super::Radix<true>>("log10", decided_by::<true>, &workloads);
}
