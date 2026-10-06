#!/usr/bin/env python3
"""The argument reduction of sin and cos (docs/sin_cos.md, section 3): the
bits of 2/pi Payne-Hanek needs, and the closest any binary64 argument comes to
a multiple of pi/2, which decides how many.

Writes crates/morphiq-numerics/src/trig/reduction.rs; with --check, fails if
the committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the bound for
generators/trig_certificates.py.

**The closest approach.** For x = m 2^E with 2^52 <= m < 2^53, x (2/pi) - k is
m alpha_E minus an integer, alpha_E = frac(2^E 2/pi). Every best approximation
of the second kind q_n of alpha_E (a continued-fraction denominator) has
||q alpha_E|| >= ||q_n alpha_E|| for 0 < q < q_(n+1) (Khinchin, Continued
Fractions, Theorem 17). So with q_n the largest denominator below 2^53,
||m alpha_E|| >= ||q_n alpha_E|| for every such m. The minimum over the
exponents with x >= pi/4 bounds |x (2/pi) - k| for every binary64 argument
the reduction sees. Computed with 4,000-bit arithmetic: alpha_E needs only
E + 53 + 200 bits of 2/pi, and the continued fraction of a 4,000-bit rational
agrees with alpha_E's far past denominators of 2^53.

**The bits kept.** For x = m 2^E, bits of 2/pi of weight above 2^(-E+1) only add
multiples of 4 m to x (2/pi), so Payne-Hanek takes the window from weight
2^(-E+1) (or the leading bit) down to 2^(-E-F). The truncation then errs by
less than m 2^-F < 2^(53-F) in x (2/pi), and F is chosen so that this is
below 2^-200 relative to the least |x (2/pi) - k|.
"""
import pathlib
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/trig/reduction.rs'
PREC = 4000
E_MIN = -53          # x >= pi/4 needs E >= -53 (m < 2^53)
E_MAX = 1023 - 52    # the largest binary64 exponent of m 2^E


def two_over_pi_int(bits):
    """floor(2/pi 2^bits), exactly enough: computed at bits + 64."""
    with mpmath.workprec(bits + 64):
        return int(mpmath.floor(2 / mpmath.pi * mpmath.mpf(2) ** bits))


def nearest_distance(q, a, scale):
    """||q a / 2^scale||, exactly, for integers q, a."""
    r = (q * a) % (1 << scale)
    return min(r, (1 << scale) - r)


def closest_approach():
    """min over E of ||q_n alpha_E||, and the E and q_n attaining it."""
    scale = PREC
    full = two_over_pi_int(scale + E_MAX + 64)  # 2/pi 2^(scale + E_MAX + 64)
    best = None
    for E in range(E_MIN, E_MAX + 1):
        # alpha_E = frac(2^E 2/pi), as a / 2^scale.
        a = (full >> (E_MAX + 64 - E)) & ((1 << scale) - 1)
        # Continued fraction of a / 2^scale, denominators until >= 2^53.
        num, den = a, 1 << scale
        q_prev, q = 0, 1
        last = 1
        while num:
            t = den // num
            den, num = num, den - t * num
            q_prev, q = q, t * q + q_prev
            if q >= 1 << 53:
                break
            last = q
        d = nearest_distance(last, a, scale)
        if best is None or d < best[0]:
            best = (d, E, last)
    d, E, q = best
    return mpmath.mpf(d) / mpmath.mpf(2) ** scale, E, q


def derive():
    mpmath.mp.prec = PREC
    d_min, E, q = closest_approach()
    # F: the truncation, below 2^(53 - F), at most 2^-200 relative to d_min.
    F = 53 + 200 + int(-mpmath.floor(mpmath.log(d_min, 2)))
    # The table: weights 2^-1 .. 2^-(E_MAX + F + 64), whole 64-bit words.
    bits = E_MAX + F + 64
    words = -(-bits // 64)
    table = two_over_pi_int(64 * words)
    # pi/2 as a 256-bit significand m 2^e, rounded to nearest.
    with mpmath.workprec(600):
        half_pi = mpmath.pi / 2
        e = int(mpmath.floor(mpmath.log(half_pi, 2))) - 255
        m = int(mpmath.nint(half_pi / mpmath.mpf(2) ** e))
        half_pi_err = abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - half_pi) / half_pi
    assert m >> 255 == 1 and half_pi_err < mpmath.mpf(2) ** -255
    return dict(d_min=d_min, E=E, q=q, F=F, words=words, table=table,
                half_pi=(m, e), half_pi_err=half_pi_err)


def generate():
    d = derive()
    w = d['words']
    limbs = [(d['table'] >> (64 * (w - 1 - i))) & ((1 << 64) - 1) for i in range(w)]
    lines = [
        '//! Payne-Hanek\'s constants for `sin` and `cos`, written by',
        '//! `generators/trig_reduction.py`; do not edit. `docs/sin_cos.md` §3 gives the',
        '//! derivation.',
        '',
        f'/// Every binary64 `x >= pi/4` has `|x (2/pi) - k| >= 2^{float(mpmath.log(d["d_min"], 2)):.2f}` for every integer `k`:',
        f'/// the least, at `x = {d["q"]} 2^{d["E"]}`, by continued fractions.',
        f'pub(super) const FRACTION_BITS: u32 = {d["F"]};',
        f'/// `2/pi` to `{64 * w}` bits: `TWO_OVER_PI[i]` holds the weights',
        '/// `2^-(64 i + 1)` to `2^-(64 i + 64)`, most significant first.',
        f'pub(super) const TWO_OVER_PI: [u64; {w}] = [',
        *[f'    0x{x:016x},' for x in limbs],
        '];',
        f'/// `pi/2` as `m 2^{d["half_pi"][1]}`, `m` in four 64-bit limbs least significant first;',
        f'/// relative error below 2^{float(mpmath.log(d["half_pi_err"], 2)):.1f}.',
        'pub(super) const HALF_PI: [u64; 4] = [',
        *[f'    0x{(d["half_pi"][0] >> (64 * i)) & ((1 << 64) - 1):016x},' for i in range(4)],
        '];',
        f'pub(super) const HALF_PI_EXPONENT: i32 = {d["half_pi"][1]};',
    ]
    return '\n'.join(lines) + '\n'


def main():
    data = generate()
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != data:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        return
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(data)


if __name__ == '__main__':
    main()
