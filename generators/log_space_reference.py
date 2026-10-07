#!/usr/bin/env python3
"""Reference cases for log_sum_exp and log_diff_exp (docs/log_space.md).

Two kinds of case:
- **exact:** the special values of docs/log_space.md §1, whose results are
  exact binary64 values (NaN payloads included where §1 specifies them);
- **bounded:** every other input. For each, the exact result y lies in a
  rigorous mpmath interval enclosure. The document's bound
  B = u·|y| + β·u·|L| + η, with β and η taken from generators/log_space_bounds.py,
  is evaluated from that enclosure in exact rational arithmetic. The allowed
  interval [y − B, y + B] is then rounded inward to binary64 endpoints lo ≤ hi.
  The check lo ≤ ŷ ≤ hi is an exact comparison with no tolerance. It is sound:
  every ŷ it accepts is within the bound. It is also exact, accepting every
  binary64 within the bound, except where y ± B lies within the enclosure's
  width of a binary64 number. There the generator cannot decide, and excludes
  that number. Terms below e^−2000 (see below) are such a case. Each bounded case also records RN(y), for
  reporting how far ŷ is from the correctly rounded result.

The enclosure uses the shifted forms y = m + ln(1 + Σ e^(xᵢ − m)) and
y = a + ln(1 − e^(b − a)), at a precision doubled from 256 bits until the
enclosure is narrower than 2^−40·B. A term whose exponent is below −2000 is
enclosed in [0, 2^−2885] instead of being evaluated, which bounds it
rigorously (e^−2000 < 2^−2885) and keeps mpmath's exponents moderate.

Writes crates/reference/fixtures/log_space.json, as flat objects for the
library tests' fixture reader: a log_sum_exp input is its elements' encodings,
space-separated, in one string. With --check, fails if the committed fixture
differs from a fresh generation. Needs mpmath
(generators/requirements.txt). Its output is integer-exact, so it does not
depend on the Python version.

Random inputs come from SplitMix64 (Steele, Lea and Flood, OOPSLA 2014).
"""
import json
import math
import pathlib
import sys
from fractions import Fraction as F

import mpmath
from mpmath import iv

from log_space_bounds import (CLAIM_DIFF_BETA, CLAIM_DIFF_ETA, CLAIM_LSE_BETA,
                              CLAIM_LSE_N_MAX, claim_lse_eta)
from oracle import from_bits, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/log_space.json'

U = F(1, 2**53)
MAX = 1.7976931348623157e308
F_MAX = F(MAX)
INF = math.inf
NAN_A = from_bits(0x7FF8000000000123)  # quiet NaNs with distinct payloads
NAN_B = from_bits(0x7FF8000000000456)
T = -0.6931471805599453  # RN(−ln 2), docs/log_space.md decision 6
DROP = -2000


def hex64(x):
    return format(to_bits(x), '016x')


def frac(raw):
    """An mpmath interval endpoint's raw (sign, man, exp, bc) tuple, exactly."""
    sign, man, exp, _ = raw
    man, exp = int(man), int(exp)
    if man == 0:
        return F(0)
    v = F(man * 2**exp) if exp >= 0 else F(man, 2**-exp)
    return -v if sign else v


def ends(y):
    lo, hi = y._mpi_
    return frac(lo), frac(hi)


def rd(q):
    """The largest binary64 ≤ q."""
    if q > F_MAX:
        return MAX
    if q < -F_MAX:
        return -INF
    f = float(q)  # CPython rounds an exact fraction to nearest
    if F(f) > q:
        f = math.nextafter(f, -INF)
    return f


def ru(q):
    """The smallest binary64 ≥ q."""
    return -rd(-q)


def abs_min(lo, hi):
    """The least |v| over [lo, hi]."""
    if lo <= 0 <= hi:
        return F(0)
    return min(abs(lo), abs(hi))


def drop_enclosure():
    return iv.mpf([0, iv.mpf(2) ** -2885])


def lse_enclosure(xs):
    """(y, L) enclosures for finite xs with at least two elements."""
    m = max(xs)
    j = xs.index(m)
    t = iv.mpf(0)
    for i, x in enumerate(xs):
        if i == j:
            continue
        d = iv.mpf(x) - iv.mpf(m)
        t += drop_enclosure() if d.b < DROP else iv.exp(d)
    big_l = iv.log(1 + t)
    return iv.mpf(m) + big_l, big_l


def diff_enclosure(a, b):
    """(y, L) enclosures for finite b < a."""
    d = iv.mpf(b) - iv.mpf(a)
    w = drop_enclosure() if d.b < DROP else iv.exp(d)
    big_l = iv.log(1 - w)
    return iv.mpf(a) + big_l, big_l


def bounded(enclose, beta, eta, label):
    """The inward-rounded allowed interval and RN(y)."""
    prec = 256
    while True:
        iv.prec = prec
        y, big_l = enclose()
        y_lo, y_hi = ends(y)
        l_lo, l_hi = ends(big_l)
        b_lo = U * abs_min(y_lo, y_hi) + beta * U * abs_min(l_lo, l_hi) + eta
        narrow = (y_hi - y_lo) <= b_lo / 2**40
        if narrow and float(y_lo) == float(y_hi):
            break
        prec *= 2
        if prec > 1 << 16:
            sys.exit(f'{label}: enclosure did not narrow by {1 << 16} bits')
    lo, hi = ru(y_hi - b_lo), rd(y_lo + b_lo)
    rn = float(y_lo)  # nearest, ties to even; y_lo and y_hi round alike
    assert lo <= rn <= hi, f'{label}: RN(y) outside the allowed interval'
    return {'lo': hex64(lo), 'hi': hex64(hi), 'rn': hex64(rn)}


def lse_case(xs, label=None):
    finite = [x for x in xs if math.isfinite(x)]
    k = len(finite) - 1
    assert 2 <= len(finite) <= CLAIM_LSE_N_MAX
    case = {'x': ' '.join(hex64(x) for x in xs)}
    if label:
        case['label'] = label
    case.update(bounded(lambda: lse_enclosure(finite), CLAIM_LSE_BETA,
                        claim_lse_eta(k), label or str(xs[:3])))
    return case


def diff_case(a, b, label=None):
    assert math.isfinite(a) and math.isfinite(b) and b < a
    case = {'a': hex64(a), 'b': hex64(b)}
    if label:
        case['label'] = label
    case.update(bounded(lambda: diff_enclosure(a, b), CLAIM_DIFF_BETA,
                        CLAIM_DIFF_ETA, label or f'({a!r}, {b!r})'))
    return case


def lse_exact():
    """docs/log_space.md §1, log_sum_exp table."""
    cases = [
        ([], -INF),
        ([-INF], -INF),
        ([-INF, -INF], -INF),
        ([NAN_A], NAN_A),
        ([1.0, NAN_A, NAN_B], NAN_A),
        ([INF, NAN_A], NAN_A),
        ([NAN_B, INF, NAN_A], NAN_B),
        ([INF], INF),
        ([INF, 1.0], INF),
        ([-INF, INF], INF),
        ([INF, INF], INF),
    ]
    for x in (0.0, -0.0, 1.5, -800.0, 5e-324, -5e-324, MAX, -MAX, 1e-300):
        cases.append(([x], x))
        cases.append(([-INF, x, -INF], x))
    return [{'x': ' '.join(hex64(v) for v in xs), 'y': hex64(y)} for xs, y in cases]


def diff_exact():
    """docs/log_space.md §1, log_diff_exp table. A result of None is any NaN."""
    cases = [
        (NAN_A, 1.0, NAN_A),
        (1.0, NAN_A, NAN_A),
        (NAN_A, NAN_B, NAN_A),
        (NAN_A, INF, NAN_A),
        (1.0, 2.0, None),
        (-INF, 3.0, None),
        (-0.0, 5e-324, None),
        (INF, INF, None),
        (-INF, -INF, -INF),
        (3.0, -INF, 3.0),
        (-0.0, -INF, -0.0),
        (MAX, -INF, MAX),
        (INF, 5.0, INF),
        (INF, -INF, INF),
    ]
    for a in (0.0, -0.0, 1.5, -700.0, 5e-324, MAX, -MAX):
        cases.append((a, a, -INF))
    out = []
    for a, b, y in cases:
        case = {'a': hex64(a), 'b': hex64(b)}
        case['y'] = 'nan' if y is None else hex64(y)
        out.append(case)
    return out


def lse_bounded():
    two_1021 = 2.0**1021
    hand = [
        ([0.0, 0.0], 'ln 2'),
        ([1.0, 1.0, 1.0, 1.0], '1 + ln 4'),
        ([T, T], 'cancellation: m = RN(-ln 2), y = m + ln 2 near 0'),
        ([-0.5, -1.2], 'partial cancellation'),
        ([0.0, -744.0], 'subnormal term'),
        ([0.0, -745.1], 'term at the underflow threshold'),
        ([0.0, -746.0], 'term underflows to +0'),
        ([0.0, -800.0], 'dropped term; t-hat = 0 returns m'),
        ([-1000.0, -1745.5], 'large shift, term underflows'),
        ([MAX, MAX], 'MAX + ln 2 rounds to MAX'),
        ([MAX, 0.0], 'operand beyond 2^1020, decision 3'),
        ([two_1021, two_1021], 'both beyond 2^1020, equal'),
        ([two_1021, math.nextafter(two_1021, 0.0)], 'beyond 2^1020, one ulp apart'),
        ([-MAX, -MAX], 'both -MAX'),
        ([5e-324, 0.0], 'subnormal operand'),
        ([1e-300, -1e-300], 'tiny operands'),
        ([-3000.1, -3000.2, -2999.9], 'log-likelihood scale'),
        ([3.0] * 1000, 'n = 1000 equal: 3 + ln 1000'),
        ([-INF, 2.0, -INF, 2.5], 'zero mass mixed with finite'),
        ([MAX, -MAX], 'x - m overflows to -inf; term skipped'),
        ([0.0] + [-2.302585092994046] * 999,
         'n = 1000, terms near 0.1: uncompensated summation drifts'),
    ]
    # Cancellation family: e^m + e^b = 1, so y is near 0 and the bound's
    # absolute term dominates; the two_sum tail dl is visible here.
    for i in range(30):
        m = -(2.0 ** (-10 + 14.5 * i / 29))  # from -2^-10 to about -22.6
        with mpmath.workprec(256):
            b = float(mpmath.log(-mpmath.expm1(mpmath.mpf(m))))
        hand.append(([m, b], 'cancellation family: e^m + e^b = 1'))
    cases = [lse_case(xs, label) for xs, label in hand]
    rng = splitmix64(0x1095_0E44)
    scales = [1.0, 30.0, 800.0, 1e5, 1e300]

    def uniform():
        return (next(rng) >> 11) * 2.0**-53

    for i in range(400):
        scale = scales[i % len(scales)]
        x1 = scale * (2 * uniform() - 1)
        gap = 2.0 ** (-60 + 72 * uniform())  # log-uniform in [2^-60, 2^12]
        cases.append(lse_case([x1, x1 - gap]))
    for i in range(200):
        n = 3 + i % 14
        scale = scales[i % len(scales)]
        centre = scale * (2 * uniform() - 1)
        spread = 2.0 ** (-20 + 32 * uniform())
        cases.append(lse_case([centre + spread * (2 * uniform() - 1) for _ in range(n)]))
    return cases


def diff_bounded():
    two_1021 = 2.0**1021
    hand = [
        (0.0, -1e-300, 'region A, tiny gap'),
        (0.0, -5e-324, 'region A, least gap at 0'),
        (1.0, math.nextafter(1.0, 0.0), 'region A, one ulp apart'),
        (0.0, T, 'boundary: d = T'),
        (0.0, math.nextafter(T, 0.0), 'boundary: just inside region A'),
        (0.0, math.nextafter(T, -INF), 'boundary: just inside region B'),
        (0.1, 0.1 + T, 'region A, inexact difference (dl != 0)'),
        (0.1, -0.6, 'region A, inexact difference'),
        (0.0, -1.0, 'region B'),
        (0.0, -30.0, 'region B'),
        (0.0, -700.0, 'region B, small w'),
        (0.0, -745.5, 'region B, w underflows'),
        (0.0, -800.0, 'region B, w = 0'),
        (0.0, -1e300, 'region B, w = 0, large gap'),
        (two_1021, math.nextafter(two_1021, 0.0), 'beyond 2^1020, one ulp apart'),
        (MAX, 0.0, 'beyond 2^1020'),
        (MAX, math.nextafter(MAX, 0.0), 'MAX, one ulp apart'),
        (0.6931471805599453, 0.0, 'cancellation: e^a - 1 near 1, y near 0'),
        (-0.3, -1.5, 'negative operands'),
        (-3000.0, -3000.5, 'log-likelihood scale'),
        (MAX, -MAX, 'b - a overflows to -inf; result a'),
    ]
    # Cancellation family: e^a - e^b = 1, so y is near 0. Small a gives
    # region B with a large |d| and a visible dl; large a gives region A.
    for i in range(30):
        a = 2.0 ** (-10 + 14.5 * i / 29)  # from 2^-10 to about 22.6
        with mpmath.workprec(256):
            b = float(mpmath.log(mpmath.expm1(mpmath.mpf(a))))
        hand.append((a, b, 'cancellation family: e^a - e^b = 1'))
    cases = [diff_case(a, b, label) for a, b, label in hand]
    rng = splitmix64(0x1095_D1FF)
    scales = [1.0, 30.0, 800.0, 1e5, 1e300]

    def uniform():
        return (next(rng) >> 11) * 2.0**-53

    for i in range(400):
        scale = scales[i % len(scales)]
        a = scale * (2 * uniform() - 1)
        gap = 2.0 ** (-70 + 82 * uniform())  # log-uniform in [2^-70, 2^12]
        b = a - gap
        if b == a:
            b = math.nextafter(a, -INF)
        cases.append(diff_case(a, b))
    return cases


def generate():
    return {
        'generator': 'generators/log_space_reference.py',
        'oracle': 'mpmath 1.4.1 interval arithmetic, from 256 bits, doubled until the '
                  'enclosure of y is narrower than 2^-40 of the allowed error',
        'bounds': {
            'sum': 'u|y| + (3 + 2^-8)·u·|L| + (2k + 1)·2^-1074, n <= 2^20 + 1',
            'difference': 'u|y| + 3.89·u·|L| + 5·2^-1074',
            'from': 'generators/log_space_bounds.py; docs/log_space.md sections 4 and 6',
        },
        'check': 'a bounded case passes if lo <= y-hat <= hi: lo and hi are the allowed '
                 'interval rounded inward, so every accepted y-hat is within the bound; '
                 'an endpoint within the enclosure width of y +/- B excludes that number; '
                 'rn is RN(y), for reporting',
        'sources': [
            'docs/log_space.md section 1 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'log_sum_exp': {'exact': lse_exact(), 'bounded': lse_bounded()},
        'log_diff_exp': {'exact': diff_exact(), 'bounded': diff_bounded()},
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
