//! Writes the Q cross-check corpus: `Q128` and `Q256` operations on
//! reproducible inputs, with this crate's results. `scripts/check_formal.sh`
//! runs the proved transcriptions (`formal/q`, extracted by
//! `formal/extraction/QCrosscheck.v`) on the same inputs and requires
//! identical results, which ties the proofs to this code.
//!
//! Ignored by default; run with the output path in `MORPHIQ_Q_CORPUS`:
//! `cargo test -p morphiq-numerics --lib q_crosscheck -- --ignored`.
//!
//! A value is written `n e k l1 .. lk`: its sign (0 or 1), its exponent in
//! decimal, its limb count and its 64-bit limbs in hex, least significant
//! first. Each line is `op args : result`.

use crate::q128::Q128;
use crate::q256::Q256;
use crate::random::SplitMix64;
use std::fmt::Write as _;
use std::string::String;

fn q128(q: Q128) -> String {
    let (n, m, e) = q.parts();
    #[allow(clippy::cast_possible_truncation)] // the low limb
    let lo = m as u64;
    std::format!("{} {e} 2 {lo:016x} {:016x}", u8::from(n), (m >> 64) as u64)
}

fn q256(q: Q256) -> String {
    let (n, m, e) = q.parts();
    std::format!(
        "{} {e} 4 {:016x} {:016x} {:016x} {:016x}",
        u8::from(n),
        m[0],
        m[1],
        m[2],
        m[3]
    )
}

/// An exponent: mostly near the operands' scale, sometimes across binary64's
/// whole range and past it, for the conversions.
fn exponent(rng: &mut SplitMix64, width: i32) -> i32 {
    let span = if rng.next_u64().is_multiple_of(4) {
        2600
    } else {
        200
    };
    i32::try_from(rng.next_u64() % span).unwrap() - i32::try_from(span / 2).unwrap() - width
}

fn r128(rng: &mut SplitMix64) -> Q128 {
    let m = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    let m = match rng.next_u64() % 8 {
        0 => 0,
        1 => m >> (rng.next_u64() % 128),
        _ => m,
    };
    Q128::new(rng.next_u64() & 1 == 1, m, exponent(rng, 127))
}

fn r256(rng: &mut SplitMix64) -> Q256 {
    let mut m = [
        rng.next_u64(),
        rng.next_u64(),
        rng.next_u64(),
        rng.next_u64(),
    ];
    match rng.next_u64() % 8 {
        0 => m = [0; 4],
        1 => m[usize::try_from(rng.next_u64() % 4).unwrap()] = 0,
        2 => {
            m[1] = u64::MAX;
            m[2] = u64::MAX;
        }
        _ => {}
    }
    Q256::new(rng.next_u64() & 1 == 1, m, exponent(rng, 255))
}

#[test]
#[ignore = "writes the Q cross-check corpus for scripts/check_formal.sh"]
fn q_crosscheck_corpus() {
    let path = std::env::var("MORPHIQ_Q_CORPUS").expect("MORPHIQ_Q_CORPUS");
    let mut rng = SplitMix64::new(0x7163_726f_7373_0001);
    let mut out = String::new();
    for _ in 0..4000 {
        let (a, b) = (r128(&mut rng), r128(&mut rng));
        // Cancellation: b near −a.
        let b = if rng.next_u64().is_multiple_of(4) {
            a.neg().add(b.mul_pow2(-100))
        } else {
            b
        };
        writeln!(out, "q128_mul {} {} : {}", q128(a), q128(b), q128(a.mul(b))).unwrap();
        writeln!(out, "q128_add {} {} : {}", q128(a), q128(b), q128(a.add(b))).unwrap();
        writeln!(
            out,
            "q128_to_f64 {} : {:016x}",
            q128(a),
            a.to_f64().to_bits()
        )
        .unwrap();
        let bits = rng.next_u64();
        writeln!(
            out,
            "q128_from_f64 {bits:016x} : {}",
            q128(Q128::from_f64(f64::from_bits(bits)))
        )
        .unwrap();

        let (c, d) = (r256(&mut rng), r256(&mut rng));
        let d = if rng.next_u64().is_multiple_of(4) {
            c.neg()
                .add(d.mul(Q256::from_f64(f64::from_bits(0x3cb0_0000_0000_0000))))
        } else {
            d
        };
        writeln!(out, "q256_mul {} {} : {}", q256(c), q256(d), q256(c.mul(d))).unwrap();
        writeln!(out, "q256_add {} {} : {}", q256(c), q256(d), q256(c.add(d))).unwrap();
        writeln!(
            out,
            "q256_to_f64 {} : {:016x}",
            q256(c),
            c.to_f64().to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "q256_from_f64 {bits:016x} : {}",
            q256(Q256::from_f64(f64::from_bits(bits)))
        )
        .unwrap();
        let k = usize::try_from(rng.next_u64() % 12).unwrap();
        let limbs: std::vec::Vec<u64> = (0..k)
            .map(|_| {
                if rng.next_u64().is_multiple_of(5) {
                    0
                } else {
                    rng.next_u64() >> (rng.next_u64() % 64)
                }
            })
            .collect();
        let neg = rng.next_u64() & 1 == 1;
        let e = exponent(&mut rng, 0);
        let hex: std::vec::Vec<String> = limbs.iter().map(|l| std::format!("{l:016x}")).collect();
        writeln!(
            out,
            "q256_from_limbs {} {e} {k} {} : {}",
            u8::from(neg),
            hex.join(" "),
            q256(Q256::from_limbs(neg, &limbs, e))
        )
        .unwrap();
    }
    std::fs::write(path, out).unwrap();
}
