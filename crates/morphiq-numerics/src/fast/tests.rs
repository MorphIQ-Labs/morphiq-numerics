use super::{elementary, normal};

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
        -8.0,
        -1.0,
        -0.5,
        -normal::MIN_MAGNITUDE,
        normal::MIN_MAGNITUDE,
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
        (elementary::ln, elementary::ln_slice),
        (normal::erfcx, normal::erfcx_slice),
        (normal::norm_cdf, normal::norm_cdf_slice),
    ] {
        for n in [0, 1, 2, 3, 7, 8, 9, 51, 52, 53, 256, 257] {
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
}
