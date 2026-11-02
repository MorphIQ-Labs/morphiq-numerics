use super::{elementary, normal};

/// The largest `a` whose `RN(a * INV_SQRT2_HIGH)` takes the CDF body.
fn cdf_body_edge() -> f64 {
    let inv = crate::normal_distribution::INV_SQRT2_HIGH;
    let mut a = super::cdf::BODY_LIMIT / inv;
    while a * inv <= super::cdf::BODY_LIMIT {
        a = a.next_up();
    }
    while a * inv > super::cdf::BODY_LIMIT {
        a = a.next_down();
    }
    a
}

#[test]
fn mixed_slices_preserve_fast_scalar_bits_and_remainders() {
    let mut xs = [0.0; 257];
    let mut word = 0x3f17_aa56_6390_87ab_u64;
    for x in &mut xs {
        word ^= word << 13;
        word ^= word >> 7;
        word ^= word << 17;
        *x = f64::from_bits(word);
    }
    xs[..16].copy_from_slice(&[
        0.0,
        -0.0,
        0.5,
        -0.5,
        8.0,
        -8.0,
        16.0,
        704.0,
        -704.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::from_bits(0x7ff8_0000_1234_5678),
        f64::MIN_POSITIVE,
        1.0,
        -1.0,
        2.3,
    ]);
    let mut offset = 16;
    for boundary in [
        -704.0,
        -normal::NEG_LIMIT,
        -8.0,
        -1.0,
        -cdf_body_edge(),
        -0.5,
        -normal::MIN_MAGNITUDE,
        normal::MIN_MAGNITUDE,
        cdf_body_edge(),
        1.0,
        8.0,
        16.0,
        704.0,
    ] {
        xs[offset..offset + 3].copy_from_slice(&[
            boundary.next_down(),
            boundary,
            boundary.next_up(),
        ]);
        offset += 3;
    }
    type Slice = fn(&[f64], &mut [f64]);
    for (scalar, slice) in [
        (
            elementary::exp as fn(f64) -> f64,
            elementary::exp_slice as Slice,
        ),
        (elementary::exp_coarse, elementary::exp_coarse_slice),
        (elementary::ln, elementary::ln_slice),
        (normal::erfcx, normal::erfcx_slice),
        (normal::norm_cdf, normal::norm_cdf_slice),
        (normal::log_norm_cdf, normal::log_norm_cdf_slice),
    ] {
        for n in (0..=17).chain([51, 52, 53, 256, 257]) {
            let mut out = [0.0; 257];
            slice(&xs[..n], &mut out[..n]);
            for (x, actual) in xs[..n].iter().zip(&out[..n]) {
                assert_eq!(actual.to_bits(), scalar(*x).to_bits(), "x={x:?}");
            }
        }
    }
}

#[test]
fn ln_specials_preserve_the_strong_owner_bits() {
    for x in [
        0.0,
        -0.0,
        -1.0,
        f64::NEG_INFINITY,
        f64::INFINITY,
        1.0,
        f64::from_bits(0x7ff8_1234_5678_9abc),
        f64::from_bits(0xfff0_1234_5678_9abc),
    ] {
        assert_eq!(
            elementary::ln(x).to_bits(),
            crate::elementary::ln(x).to_bits()
        );
    }
}

#[test]
#[should_panic(expected = "ln_slice: slices of different lengths")]
fn ln_slice_rejects_length_mismatch() {
    elementary::ln_slice(&[1.0], &mut []);
}

#[test]
fn unaccelerated_inputs_retain_strong_results() {
    for x in [
        -745.0,
        -704.0,
        704.0,
        709.0,
        f64::NEG_INFINITY,
        f64::INFINITY,
    ] {
        assert_eq!(
            elementary::exp(x).to_bits(),
            crate::elementary::exp(x).to_bits()
        );
        assert_eq!(
            elementary::exp_coarse(x).to_bits(),
            crate::elementary::exp(x).to_bits()
        );
    }
    for x in [
        -38.0,
        -8.0_f64.next_up(),
        0.0,
        -0.0,
        8.0_f64.next_up(),
        38.0,
    ] {
        assert_eq!(
            normal::norm_cdf(x).to_bits(),
            crate::normal::norm_cdf(x).to_bits()
        );
    }
    for x in [-26.0, -0.5_f64.next_up(), 0.0, -0.0, 16.0, 512.0, f64::MAX] {
        assert_eq!(
            normal::erfcx(x).to_bits(),
            crate::normal::erfcx(x).to_bits()
        );
    }
    for x in [
        -40.0,
        -normal::NEG_LIMIT.next_up(),
        -normal::MIN_MAGNITUDE.next_down(),
        0.0,
        -0.0,
        normal::MIN_MAGNITUDE.next_down(),
        8.0_f64.next_up(),
        40.0,
        f64::NEG_INFINITY,
        f64::INFINITY,
        f64::from_bits(0x7ff8_1234_5678_9abc),
        f64::from_bits(0xfff8_0000_0000_0001),
    ] {
        assert_eq!(
            normal::log_norm_cdf(x).to_bits(),
            crate::normal::log_norm_cdf(x).to_bits(),
            "x={x:?}"
        );
    }
}

/// The accelerated log-CDF agrees with the strong owner to the published
/// log-unit budget, is negative, finite and normal, and the two sides of its
/// scalar branch meet the strong value at the same scale around zero.
#[test]
fn log_cdf_accelerated_domain_tracks_the_strong_owner() {
    let budget = |strong: f64| {
        f64::from_bits(0x3cc0_0000_0000_0000) * strong.abs() + f64::from_bits(0x3cf0_0000_0000_0000)
    };
    let mut worst = 0.0_f64;
    for i in 0..=45_000 {
        let x = -normal::NEG_LIMIT + (normal::NEG_LIMIT + 8.0) * f64::from(i) / 45_000.0;
        if x.abs() < normal::MIN_MAGNITUDE {
            continue;
        }
        let fast = normal::log_norm_cdf(x);
        let strong = crate::normal::log_norm_cdf(x);
        assert!(
            fast.is_finite() && fast < 0.0 && fast.is_normal(),
            "x={x:?} -> {fast:?}"
        );
        let error = (fast - strong).abs();
        worst = worst.max(error / budget(strong));
        assert!(
            error <= budget(strong),
            "x={x:?}: fast {fast:?} strong {strong:?}"
        );
    }
    // The strong owner is itself within 2^-53 relative; this is a sampled
    // sanity check against the published budget, not the proof of it.
    assert!(worst < 1.0);
}

#[test]
#[should_panic(expected = "exp_coarse_slice: slices of different lengths")]
fn exp_coarse_slice_rejects_length_mismatch() {
    elementary::exp_coarse_slice(&[1.0], &mut []);
}

#[test]
fn the_two_exp_kernels_are_distinct_and_exact_at_zero() {
    // Zero is exact in both; elsewhere the kernels are different approximations,
    // so a coincidence everywhere would mean one entry routes to the other.
    assert_eq!(elementary::exp(0.0).to_bits(), 1.0_f64.to_bits());
    assert_eq!(elementary::exp_coarse(0.0).to_bits(), 1.0_f64.to_bits());
    let differs = (1..=64)
        .map(|i| f64::from(i) * 0.03125 - 1.0)
        .any(|x| elementary::exp(x).to_bits() != elementary::exp_coarse(x).to_bits());
    assert!(differs);
}
