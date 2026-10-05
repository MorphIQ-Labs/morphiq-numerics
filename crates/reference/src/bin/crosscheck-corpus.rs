//! Writes the cross-check corpus: each public double-word operation and
//! error-free transform on reproducible inputs, with the library's results.
//!
//! `scripts/check_formal.sh` runs the proved IEEE 754 definitions, extracted
//! from Coq, on the same inputs and requires identical bits
//! (`formal/extraction`). The inputs cover the proved domains and go beyond
//! them, into overflow, subnormals, zeros and signed zeros: the Rust code and
//! its Coq transcription must agree everywhere, not only where the bounds hold.
//!
//! Each line is `op in... : out out`, every value a binary64 as 16 hex digits.

use std::io::{BufWriter, Write};

use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics::eft::{fast_two_sum, two_prod, two_sum};
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

fn pair(z: DoubleWord) -> (f64, f64) {
    (z.hi(), z.lo())
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
    }
    out.flush().expect("flush");
}
