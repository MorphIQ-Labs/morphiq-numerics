//! Writes the cross-check corpus: each public double-word operation (including
//! `exp_split`) and error-free transform, `sqrt` and the slice reductions, on
//! reproducible inputs, with the library's results.
//!
//! `scripts/check_formal.sh` runs the proved IEEE 754 definitions, extracted
//! from Coq, on the same inputs and requires identical bits
//! (`formal/extraction`). The inputs cover the proved domains and go beyond
//! them, into overflow, subnormals, zeros and signed zeros: the Rust code and
//! its Coq transcription must agree everywhere, not only where the bounds hold.
//!
//! Each line is `op in... : out...`, every value a binary64 as 16 hex digits.
//! A reduction's inputs are its slice, or `x` followed by `y`.

use std::io::{BufWriter, Write};

use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics::eft::{fast_two_sum, two_prod, two_sum};
use morphiq_numerics::elementary::sqrt;
use morphiq_numerics::reduce;
use morphiq_numerics_reference::Words;

/// Cases per operation.
const CASES: usize = 4000;

/// A word: mostly normal with an exponent in `[low, high]`; sometimes zero,
/// negative zero or subnormal.
fn word(words: &mut Words, low: i64, high: i64) -> f64 {
    match words.next_word() % 16 {
        0 => 0.0,
        1 => -0.0,
        2 => {
            let bits = words.next_word() & ((1 << 52) - 1) | (words.next_word() & (1 << 63));
            f64::from_bits(bits)
        }
        _ => {
            let span = u64::try_from(high - low + 1).unwrap();
            let e = low + i64::try_from(words.next_word() % span).unwrap();
            words.with_exponent(e)
        }
    }
}

/// A double-word number: a leading word and a trailing word 53 to 60 binades
/// below it, normalized by `DoubleWord::sum`.
fn double_word(words: &mut Words, low: i64, high: i64) -> DoubleWord {
    let hi = word(words, low, high);
    // The leading word's unbiased exponent; zero and subnormals count as -1022.
    let e_hi = i64::try_from((hi.to_bits() >> 52) & 0x7ff).unwrap().max(1) - 1023;
    let k = i64::try_from(words.next_word() % 8).unwrap();
    let e = (e_hi - 53 - k).max(-1022);
    let lo = word(words, e, e);
    DoubleWord::sum(hi, lo)
}

/// The exponent range for one case: three quarters near the proved domains,
/// one quarter across nearly the whole range.
fn range(words: &mut Words) -> (i64, i64) {
    if words.next_word().is_multiple_of(4) {
        (-1000, 1020)
    } else {
        (-200, 200)
    }
}

fn hex(x: f64) -> String {
    format!("{:016x}", x.to_bits())
}

fn line(out: &mut impl Write, op: &str, ins: &[f64], (h, l): (f64, f64)) {
    let ins: Vec<String> = ins.iter().map(|&x| hex(x)).collect();
    writeln!(out, "{op} {} : {} {}", ins.join(" "), hex(h), hex(l)).expect("write");
}

fn line1(out: &mut impl Write, op: &str, x: f64, r: f64) {
    writeln!(out, "{op} {} : {}", hex(x), hex(r)).expect("write");
}

fn pair(z: DoubleWord) -> (f64, f64) {
    (z.hi(), z.lo())
}

/// `exp_split`: a presence flag, the value's words and the exponent offset by
/// 4096 (so it is a small positive word, never a NaN's bits), or four zeros
/// for `None`.
fn exp_split_line(out: &mut impl Write, x: DoubleWord) {
    let outs = match x.exp_split() {
        Some((value, n)) => [
            1,
            value.hi().to_bits(),
            value.lo().to_bits(),
            u64::try_from(i64::from(n) + 4096).expect("|n| < 4096"),
        ],
        None => [0; 4],
    };
    let outs: Vec<String> = outs.iter().map(|w| format!("{w:016x}")).collect();
    writeln!(
        out,
        "exp_split {} {} : {}",
        hex(x.hi()),
        hex(x.lo()),
        outs.join(" ")
    )
    .expect("write");
}

/// One element of a reduction's slice. `class` selects the case's regime, so a
/// whole slice can be ordinary, near overflow or underflow, or non-finite.
fn element(words: &mut Words, class: u64) -> f64 {
    match class {
        // Magnitudes whose sums or products overflow.
        0 => word(words, 500, 1023),
        // Products at and below the underflow limits.
        1 => word(words, -560, -400),
        // Infinities and NaNs with payloads among ordinary terms.
        2 if words.next_word().is_multiple_of(4) => {
            let payload = words.next_word() & ((1 << 52) - 1);
            let sign = words.next_word() & (1 << 63);
            let payload = if words.next_word().is_multiple_of(3) {
                0
            } else {
                payload
            };
            f64::from_bits(sign | (0x7ff << 52) | payload)
        }
        _ => word(words, -60, 60),
    }
}

/// Every slice reduction on one pair of slices. Every other term of some cases
/// nearly cancels the one before it.
fn reduction_lines(out: &mut impl Write, words: &mut Words, n: usize) {
    let class = words.next_word() % 6;
    let mut x: Vec<f64> = (0..n).map(|_| element(words, class)).collect();
    let y: Vec<f64> = (0..n).map(|_| element(words, class)).collect();
    if class == 5 {
        for i in (1..n).step_by(2) {
            x[i] = -x[i - 1].next_up();
        }
    }
    let mut emit = |op: &str, ins: &[&[f64]], result: f64| {
        let ins: String = ins
            .iter()
            .flat_map(|s| s.iter())
            .map(|&v| format!(" {}", hex(v)))
            .collect();
        writeln!(out, "{op}{ins} : {}", hex(result)).expect("write");
    };
    emit("sum", &[&x], reduce::sum(&x));
    emit("sum2", &[&x], reduce::sum2(&x));
    emit("dot", &[&x, &y], reduce::dot(&x, &y));
    emit("dot2", &[&x, &y], reduce::dot2(&x, &y));
    emit("sum_squares", &[&x], reduce::sum_squares(&x));
    emit("sum_squares2", &[&x], reduce::sum_squares2(&x));
    emit("max_abs", &[&x], reduce::max_abs(&x));
}

fn main() {
    let mut words = Words::new(0x0c0c_c705_5c4e_c401);
    let mut out = BufWriter::new(std::io::stdout().lock());
    for _ in 0..CASES {
        let (low, high) = range(&mut words);
        let (a, b) = (word(&mut words, low, high), word(&mut words, low, high));
        line(&mut out, "two_sum", &[a, b], two_sum(a, b));
        line(&mut out, "fast_two_sum", &[a, b], fast_two_sum(a, b));
        line(&mut out, "two_prod", &[a, b], two_prod(a, b));

        let x = double_word(&mut words, low, high);
        let y = double_word(&mut words, low, high);
        let f = word(&mut words, low, high);
        let (xh, xl, yh, yl) = (x.hi(), x.lo(), y.hi(), y.lo());
        line(&mut out, "add_f64", &[xh, xl, f], pair(x.add_f64(f)));
        line(&mut out, "add", &[xh, xl, yh, yl], pair(x.add(y)));
        line(&mut out, "sub", &[xh, xl, yh, yl], pair(x.sub(y)));
        line(&mut out, "mul_f64", &[xh, xl, f], pair(x.mul_f64(f)));
        line(&mut out, "mul", &[xh, xl, yh, yl], pair(x.mul(y)));
        line(&mut out, "div_f64", &[xh, xl, f], pair(x.div_f64(f)));
        line(&mut out, "div", &[xh, xl, yh, yl], pair(x.div(y)));
        // Mostly inside exp_split's domain |hi| < 1455, its reduction seams and
        // its tiny-argument switch, sometimes beyond it.
        exp_split_line(&mut out, double_word(&mut words, -70, 10));
        exp_split_line(&mut out, x);

        // Every encoding: both signs, the subnormals, infinities and NaNs.
        let any = f64::from_bits(words.next_word());
        line1(&mut out, "sqrt", any, sqrt(any));
        let positive = word(&mut words, low, high).abs();
        line1(&mut out, "sqrt", positive, sqrt(positive));
    }
    for special in [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        1455.0,
        -1455.0,
        1454.999,
        -1454.999,
    ] {
        exp_split_line(&mut out, DoubleWord::from_f64(special));
    }
    // Every short length, the empty slice included, then longer ones.
    for case in 0..CASES {
        let n = if case % 40 == 39 {
            33 + case % 97
        } else {
            case % 9
        };
        reduction_lines(&mut out, &mut words, n);
    }
    out.flush().expect("flush");
}
