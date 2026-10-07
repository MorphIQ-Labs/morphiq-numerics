#!/usr/bin/env python3
"""Constants for log_norm_pdf (docs/log_norm_pdf.md §2–§3), and the facts about
them the derivation relies on.

C = ln √(2π) = ln(2π)/2, as the double-word C_HI + C_LO: C_HI = RN(C) and
C_LO = RN(C − C_HI). The script asserts, in exact rational arithmetic on a
rigorous mpmath interval enclosure of C:

- |C − C_HI − C_LO| ≤ 2^−107·C, the truncation error §3 charges;
- C_HI + ulp(C_HI)/2 − C, the distance from C up to the next rounding midpoint,
  exceeds 2^−55, so RN(C + x²/2) = C_HI whenever x²/2 < 2^−55 (§2, |x| < 2^−27);
- C_HI is not a power of two and C lies in [1/2, 1), so ulp(C_HI) = 2^−53.

Writes crates/morphiq-numerics/src/log_norm_pdf/tables.rs; with --check, fails
if the committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). Its output is integer-exact.
"""
import math
import pathlib
import sys
from fractions import Fraction as F

from mpmath import iv

from oracle import to_bits

OUTPUT = (pathlib.Path(__file__).resolve().parents[1]
          / 'crates/morphiq-numerics/src/log_norm_pdf/tables.rs')


def frac(raw):
    sign, man, exp, _ = raw
    man, exp = int(man), int(exp)
    v = F(man * 2**exp) if exp >= 0 else F(man, 2**-exp)
    return -v if sign else v


def enclosure():
    """C enclosed to better than 2^−300 relatively, as exact rationals."""
    iv.prec = 512
    c = iv.log(2 * iv.pi) / 2
    lo, hi = (frac(end) for end in c._mpi_)
    assert hi - lo < lo / 2**300
    return lo, hi


def nearest(q):
    """RN(q) for a positive rational q in the normal range."""
    return float(q)  # CPython rounds an exact fraction to nearest, ties to even


def generate():
    lo, hi = enclosure()
    c_hi = nearest(lo)
    assert c_hi == nearest(hi), 'RN(C) undecided'
    c_lo = nearest(lo - F(c_hi))
    assert c_lo == nearest(hi - F(c_hi)), 'RN(C − C_HI) undecided'
    assert F(1, 2) <= lo and hi < 1 and c_hi != 0.5
    ulp = F(1, 2**53)
    assert F(math.ulp(c_hi)) == ulp

    # Truncation error of the double-word.
    tail = max(abs(lo - F(c_hi) - F(c_lo)), abs(hi - F(c_hi) - F(c_lo)))
    assert tail <= lo / 2**107, 'C_HI + C_LO not within 2^−107·C'
    # Distance from C up to the next midpoint.
    gap = F(c_hi) + ulp / 2 - hi
    assert gap > F(1, 2**55), 'C too close to a midpoint for the small regime'

    tail_log2 = math.floor(math.log2(tail / lo)) if tail else None
    gap_log2 = math.floor(math.log2(gap))
    return f'''//! Constants of `log_norm_pdf`, written by `generators/log_norm_pdf_constants.py`;
//! do not edit. `C = ln √(2π)` as the double-word `C_HI + C_LO`;
//! `docs/log_norm_pdf.md` gives the derivation.
//!
//! `|C − C_HI − C_LO| < 2^{tail_log2 + 1}·C`, and `C` lies `2^{gap_log2}`
//! or more below the next rounding midpoint `C_HI + 2^−54`.

/// `RN(ln √(2π))` = {c_hi!r}.
pub(super) const C_HI: f64 = f64::from_bits(0x{to_bits(c_hi):016x});
/// `RN(ln √(2π) − C_HI)` = {c_lo!r}.
pub(super) const C_LO: f64 = f64::from_bits(0x{to_bits(c_lo):016x});
'''


def main():
    text = generate()
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != text:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        print(f'{OUTPUT.name}: matches a fresh generation')
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(text)
        print(f'wrote {OUTPUT}')


if __name__ == '__main__':
    main()
