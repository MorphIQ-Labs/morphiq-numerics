#!/usr/bin/env python3
"""Correctly rounded log_norm_pdf(x) = −x²/2 − ln √(2π) for binary64 x: the
reference values log_norm_pdf is tested against (docs/log_norm_pdf.md §6).

Each value is rounded to nearest, ties to even, into binary64 by the interval
oracle in generators/oracle (mpmath interval arithmetic, precision doubled
until both ends of the enclosure round alike, at two consecutive precisions);
overflow rounds to −∞.

The cases:
- §1's special values: NaN (its payload kept), ±∞, ±0;
- regime S far below its boundary: the least subnormal, the least normal,
  2^−600, and 2^−484 with its neighbours, below which two_prod(a, a/2) leaves
  its domain;
- each regime boundary of §1 (2^−27, 2^500, 2^512, 2^513) with its
  neighbours, both signs;
- the overflow threshold: the largest x with a finite result, found by
  bisection on the oracle, and its successor;
- ties in regime L (§4): a = m·2^k where m is odd and m² has exactly 54 bits,
  so a²/2 is a rounding midpoint and C breaks the tie away from zero; and
  each tie's neighbours;
- SplitMix64 inputs (Steele, Lea and Flood, OOPSLA 2014): 8 per binade from
  2^−40 to 2^513, both signs, and 2,000 in [−8, 8].

Writes crates/reference/fixtures/log_norm_pdf.json as flat objects; with
--check, fails if the committed fixture differs from a fresh generation. Needs
mpmath (generators/requirements.txt). Its output is integer-exact.
"""
import json
import math
import pathlib
import sys

from mpmath import iv

from oracle import bisect, correctly_rounded, from_bits, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/log_norm_pdf.json'
NAN_A = from_bits(0x7FF8000000000123)


def f(x):
    """−x²/2 − ln √(2π) on an mpmath interval."""
    return -(x * x) / 2 - iv.log(2 * iv.pi) / 2


def reference(x):
    if math.isnan(x):
        return x
    if math.isinf(x):
        return -math.inf
    return correctly_rounded(f, x)


def hex64(x):
    return format(to_bits(x), '016x')


def neighbours(x):
    return [math.nextafter(x, 0.0), x, math.nextafter(x, math.inf)]


def ties():
    """Regime-L arguments whose square halves to a rounding midpoint."""
    out = []
    lo = math.isqrt(2**53 - 1) + 1  # the least m with m² ≥ 2^53
    for m in (lo | 1, lo + 1001 | 1, 2**27 - 3, 2**27 - 1):
        assert m % 2 == 1 and (m * m).bit_length() == 54
        for k in (474, 478, 485):  # a = m·2^k in (2^500, 2^513)
            a = float(m) * 2.0**k
            assert 2.0**500 < a < 2.0**513
            out.append(a)
    return out


def overflow_threshold():
    """The largest positive x with a finite result."""
    lo, hi = to_bits(2.0**512), to_bits(2.0**513)
    assert math.isfinite(reference(from_bits(lo))) and reference(from_bits(hi)) == -math.inf
    first_overflow = bisect(lo, hi, lambda b: reference(from_bits(b)) == -math.inf)
    return from_bits(first_overflow - 1)


def inputs():
    hand = [NAN_A, math.inf, -math.inf, 0.0, -0.0]
    # Regime S far below its boundary: the least subnormal, the least normal,
    # and around 2^−484, below which two_prod(a, a/2) leaves its domain.
    for x in (5e-324, 2.0**-1022, 2.0**-600) + tuple(neighbours(2.0**-484)):
        hand += [x, -x]
    for boundary in (2.0**-27, 2.0**500, 2.0**512, 2.0**513):
        for x in neighbours(boundary):
            hand += [x, -x]
    threshold = overflow_threshold()
    for x in neighbours(threshold):
        hand += [x, -x]
    for a in ties():
        for x in neighbours(a):
            hand += [x, -x]
    rng = splitmix64(0x1095_1F0D)
    random = []
    for e in range(-40, 513):
        for _ in range(8):
            mantissa = next(rng) >> 12
            sign = next(rng) >> 63
            x = from_bits((sign << 63) | ((e + 1023) << 52) | mantissa)
            random.append(x)
    for _ in range(2000):
        random.append(16.0 * ((next(rng) >> 11) * 2.0**-53) - 8.0)
    return hand, random


def generate():
    hand, random = inputs()
    def case(x):
        return {'x': hex64(x), 'y': hex64(reference(x))}
    return {
        'generator': 'generators/log_norm_pdf_reference.py',
        'oracle': 'mpmath 1.4.1 interval arithmetic, from 128 bits, doubled until both '
                  'ends of the enclosure round alike at two consecutive precisions',
        'rounding': 'to nearest, ties to even; overflow to -inf',
        'sources': [
            'docs/log_norm_pdf.md sections 1 and 4 (special values, regime boundaries, ties)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'hand': [case(x) for x in hand],
        'random': [case(x) for x in random],
    }


def main():
    text = json.dumps(generate(), indent=1) + '\n'
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != text:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        print(f'{OUTPUT.name}: matches a fresh generation')
    else:
        OUTPUT.write_text(text)
        print(f'wrote {OUTPUT}')


if __name__ == '__main__':
    main()
