#!/usr/bin/env python3
"""The constants of asin (docs/asin.md), with their errors.

Writes crates/morphiq-numerics/src/asin/tables.rs; with --check, fails if the
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the values the certificates
use.

- SEGMENTS[k - 1], k = 1..=45 (section 4): for `a = k/64`,
    [asin(a).hi, asin(a).lo, c1.hi, c1.lo, g0, ..., g8]
  with `c1 = 1/sqrt(1 - a^2)` and `G_k`'s coefficients from
  generators/asin_poly.out, so that
    asin(a + t) = asin(a) + c1 t + t^2 (g0 + g1 t + ... + g8 t^8)
  on |t| <= 0.0078126. The double-words are `hi = RN(v)`, `lo = RN(v - hi)`.
- POLY0 (section 4): `asin z = z + z^3 (p0 + p1 z^2 + p2 z^4 + p3 z^6)` for
  z <= 0.0078126, from the same file.
- HALF_PI: pi/2 as a double-word.

Also writes formal/asin/AsinTables.v, the same constants for the Coq
transcription (formal/asin/AsinKernel.v), as binary64 encodings and `Q256`
limbs, with the `Q256` series' steps and pi/2 read from trig's committed
tables (crates/morphiq-numerics/src/trig/tables.rs, reduction.rs).

The polynomials' errors are the Sollya supnorm plus the Taylor remainder bound
of asin_poly.sollya. As a check, not a proof, the generator also evaluates
each segment's polynomial at 400 points in mpmath and refuses a deviation
larger than that bound.
"""
import math
import pathlib
import re
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/asin/tables.rs'
OUTPUT_COQ = ROOT / 'formal/asin/AsinTables.v'
TRIG_TABLES = ROOT / 'crates/morphiq-numerics/src/trig/tables.rs'
TRIG_REDUCTION = ROOT / 'crates/morphiq-numerics/src/trig/reduction.rs'
POLY = ROOT / 'generators/asin_poly.out'
PREC = 600
T = mpmath.mpf('0.0078126')  # |t| <= 1/128, widened for z's double-word error
SEGMENTS = 45                # k = round(64 z) <= round(64 sqrt(1/2)) = 45
DEGREE = 8


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rn53(v):
    v = mpmath.mpf(v)
    if v == 0:
        return 0.0
    sign = -1 if v < 0 else 1
    man, exp = abs(v).man_exp
    man = int(man)
    shift = man.bit_length() - 53
    if shift > 0:
        m, rem, half = man >> shift, man & ((1 << shift) - 1), 1 << (shift - 1)
        if rem > half or (rem == half and m & 1):
            m += 1
        exp += shift
    else:
        m = man
    return sign * math.ldexp(m, int(exp))


def read_poly():
    return {n: v for n, v in (line.split() for line in POLY.read_text().split('\n') if line.strip())}


def double_word(v):
    hi = rn53(v)
    lo = rn53(v - hi)
    return hi, lo, abs(v - hi - lo) / abs(v)


def derive():
    mpmath.mp.prec = PREC
    values = read_poly()
    rows, worst_dw, worst_poly = [], mpmath.mpf(0), mpmath.mpf(0)
    for k in range(1, SEGMENTS + 1):
        a = mpmath.mpf(k) / 64
        y = double_word(mpmath.asin(a))
        c1 = double_word(1 / mpmath.sqrt(1 - a * a))
        worst_dw = max(worst_dw, y[2], c1[2])
        g = [float.fromhex(values[f'g{k:02d}{j}']) for j in range(DEGREE + 1)]
        bound = mpmath.mpf(float.fromhex(values[f'u{k:02d}0'])) + mpmath.mpf(float.fromhex(values[f'r{k:02d}0']))
        # Not a proof: the polynomial against asin at 400 points.
        deviation = mpmath.mpf(0)
        for i in range(401):
            t = -T + 2 * T * i / 400
            p = mpmath.mpf(0)
            for c in reversed(g):
                p = p * t + mpmath.mpf(c)
            approx = mpmath.mpf(y[0]) + mpmath.mpf(y[1]) + (mpmath.mpf(c1[0]) + mpmath.mpf(c1[1])) * t + t * t * p
            deviation = max(deviation, abs(approx - mpmath.asin(a + t)))
        assert deviation <= bound * T * T * (1 + mpmath.mpf(2) ** -20) + mpmath.mpf(2) ** -105, (
            f'segment {k}: deviation {mpmath.nstr(deviation, 5)} exceeds {mpmath.nstr(bound * T * T, 5)}')
        worst_poly = max(worst_poly, bound * T * T / mpmath.asin(a - T))
        rows.append((y[0], y[1], c1[0], c1[1], *g))
    assert worst_dw < mpmath.mpf(2) ** -106
    poly0 = [float.fromhex(values[f'p0{0}{j}']) for j in range(4)]
    half_pi = double_word(mpmath.pi / 2)
    return dict(values=values, rows=rows, poly0=poly0, worst_dw=worst_dw,
                worst_poly=worst_poly, half_pi=half_pi)


def generate():
    d = derive()
    v = d['values']
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    lines = [
        '//! Constants of `asin`, written by `generators/asin_constants.py`; do not',
        '//! edit. `docs/asin.md` gives the derivation.',
        '',
        '/// `asin z ≈ z + z³·(p0 + p1 z² + p2 z⁴ + p3 z⁶)` for `0 <= z <= 0.0078126`',
        f'/// (`generators/asin_poly.sollya`): relative error of the series at most {v["v000"]}.',
        'pub(super) const POLY0: [f64; 4] = [',
        *[f'    {f(c)},' for c in d['poly0']],
        '];',
        '/// `[asin(a).hi, asin(a).lo, c1.hi, c1.lo, g0, ..., g8]` for `a = k/64`,',
        '/// `k = 1..=45` at index `k - 1`, `c1 = 1/√(1 − a²)`:',
        '/// `asin(a + t) = asin(a) + c1·t + t²·(g0 + g1·t + … + g8·t⁸)` on `|t| <= 0.0078126`.',
        f'/// The double-words have relative error below 2^{float(mpmath.log(d["worst_dw"], 2)):.1f}; the',
        '/// polynomials are bounded by `generators/asin_poly.out`.',
        f'pub(super) const SEGMENTS: [[f64; {4 + DEGREE + 1}]; {SEGMENTS}] = [',
        *[line for row in d['rows'] for line in ('    [', *[f'        {f(x)},' for x in row], '    ],')],
        '];',
        '/// `π/2` as a double-word `(hi, lo)`.',
        'pub(super) const HALF_PI: (f64, f64) = (',
        f'    {f(d["half_pi"][0])},',
        f'    {f(d["half_pi"][1])},',
        ');',
    ]
    return '\n'.join(lines) + '\n'


def trig_steps(name):
    """A `Q256` series' steps `(limbs, exponent)` from trig's tables.rs."""
    text = TRIG_TABLES.read_text()
    body = text[text.index(f'const {name}'):]
    body = body[:body.index('];')]
    steps = [([int(x, 16) for x in re.findall(r'0x([0-9a-f]+)', limbs)], int(e))
             for limbs, e in re.findall(r'\[((?:\s*0x[0-9a-f]+,){4}\s*)\],\s*(-?\d+),', body)]
    assert steps, name
    return steps


def trig_half_pi():
    """pi/2 as `Q256` limbs and exponent, from trig's reduction.rs."""
    text = TRIG_REDUCTION.read_text()
    block = text[text.index('const HALF_PI: [u64; 4]'):]
    limbs = [int(x, 16) for x in re.findall(r'0x([0-9a-f]+)', block[:block.index('];')])]
    exponent = int(re.search(r'HALF_PI_EXPONENT: i32 = (-?\d+)', text).group(1))
    assert len(limbs) == 4
    return limbs, exponent


def generate_coq():
    d = derive()
    word = lambda x: f'0x{to_bits(x):016x}'  # noqa: E731
    limb = lambda x: f'0x{x:016x}'  # noqa: E731
    def steps(name, entries):
        rows = [f'  ([{"; ".join(limb(x) for x in l)}], {e})' for l, e in entries]
        return [f'Definition {name} : list (list Z * Z) := [', ';\n'.join(rows), '].']
    half_pi_limbs, half_pi_exp = trig_half_pi()
    lines = [
        '(** Constants of asin\'s transcription, written by generators/asin_constants.py; do',
        '    not edit. docs/asin.md gives the derivation. Binary64 values are encodings; a',
        '    Q256 value is its limbs, least significant first, and an exponent. *)',
        'From Coq Require Import ZArith List.',
        'Import ListNotations.',
        'Open Scope Z_scope.',
        '',
        '(** The series polynomial below 1/128 (src/asin/tables.rs POLY0). *)',
        f'Definition asin_poly0 : list Z := [{"; ".join(word(c) for c in d["poly0"])}].',
        '(** [asin(a).hi, asin(a).lo, c1.hi, c1.lo, g0, ..., g8] for a = k/64, k = 1..45 at',
        '    index k - 1 (src/asin/tables.rs SEGMENTS). *)',
        'Definition asin_segments : list (list Z) := [',
        ';\n'.join(f'  [{"; ".join(word(x) for x in row)}]' for row in d['rows']),
        '].',
        f'Definition asin_half_pi : Z * Z := ({word(d["half_pi"][0])}, {word(d["half_pi"][1])}).',
        '(** pi/2 in Q256: limbs and exponent (src/trig/reduction.rs HALF_PI). *)',
        f'Definition asin_q_half_pi : list Z * Z := ([{"; ".join(limb(x) for x in half_pi_limbs)}], {half_pi_exp}).',
        '(** The steps of trig\'s Q256 series (src/trig/tables.rs SIN_STEPS, COS_STEPS), which',
        '    asin\'s accurate path evaluates. *)',
        *steps('asin_sin_steps', trig_steps('SIN_STEPS')),
        *steps('asin_cos_steps', trig_steps('COS_STEPS')),
    ]
    return '\n'.join(lines) + '\n'


def main():
    outputs = {OUTPUT: generate(), OUTPUT_COQ: generate_coq()}
    if '--check' in sys.argv[1:]:
        for path, data in outputs.items():
            if path.read_text() != data:
                sys.exit(f'{path} differs from a fresh generation')
        return
    for path, data in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(data)


if __name__ == '__main__':
    main()
