#!/usr/bin/env python3
"""The Gauss-Legendre rules of the bivariate normal (docs/bivariate_normal.md).

Writes crates/morphiq-numerics/src/bivariate_normal/tables.rs; with --check,
fails if the committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

For each order n in ORDERS (and ODD_ORDERS) the n/2 positive abscissas and their weights come
from the roots of the Legendre polynomial P_n, polished by Newton's method at
120 digits and rounded once to nearest-even binary64; the residual
|P_n(x)| and the weight identity sum(2 w_i) = 2 are checked at generation
time. The rounding error of each stored value is at most half an ulp, which
docs/bivariate_normal.md carries into the quadrature's error budget.
"""
import pathlib
import struct
import sys

import mpmath as mp

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/bivariate_normal/tables.rs'
ORDERS = (4, 6, 8, 10, 12, 14, 16, 20, 24)
# The odd orders of the high-correlation panels (docs/bivariate_normal_high.md):
# the (n - 1)/2 positive abscissas and weights as above, and the centre node's
# weight, whose abscissa is exactly 0.
ODD_ORDERS = (3, 5, 7, 9, 11, 13, 15)
DPS = 120


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rule(n):
    """Positive abscissas (descending) and weights of the n-point rule, and the
    weight of the centre node (None for even n)."""
    xs, ws = [], []
    for i in range(1, n // 2 + 1):
        x = mp.cos(mp.pi * (i - mp.mpf(1) / 4) / (n + mp.mpf(1) / 2))
        for _ in range(100):
            p, q = mp.legendre(n, x), mp.legendre(n - 1, x)
            dp = n * (x * p - q) / (x * x - 1)
            step = p / dp
            x -= step
            if abs(step) < mp.mpf(10) ** (-DPS + 5):
                break
        p, q = mp.legendre(n, x), mp.legendre(n - 1, x)
        dp = n * (x * p - q) / (x * x - 1)
        assert abs(mp.legendre(n, x)) < mp.mpf(10) ** (-DPS + 10), (n, i)
        xs.append(x)
        ws.append(2 / ((1 - x * x) * dp * dp))
    centre = None
    if n % 2:
        # P_n'(0) = n P_{n-1}(0) for odd n.
        dp0 = n * mp.legendre(n - 1, 0)
        centre = 2 / (dp0 * dp0)
    total = 2 * sum(ws) + (centre or 0)
    assert abs(total - 2) < mp.mpf(10) ** (-DPS + 10), n
    return xs, ws, centre


def generate():
    mp.mp.dps = DPS
    lines = [
        '//! Gauss-Legendre rules of the bivariate normal, written by',
        '//! `generators/bivariate_normal_nodes.py`; do not edit. Each rule lists the',
        '//! positive abscissas in descending order and their weights, each rounded',
        '//! once to nearest-even binary64 from the 120-digit root of `P_n`;',
        '//! `docs/bivariate_normal.md` gives the derivation.',
        '',
    ]
    for n in sorted(ORDERS + ODD_ORDERS, key=lambda n: (n % 2, n)):
        xs, ws, centre = rule(n)
        m = n // 2
        for name, values in (('X', xs), ('W', ws)):
            if name == 'X':
                lines.append(f'/// The {m} positive abscissas of the {n}-point rule')
            elif centre is None:
                lines.append(f'/// Their weights, summing to 1 over the {m} positive nodes')
            else:
                lines.append(f'/// Their weights; with the centre weight, `2 * sum + centre = 2`')
            if m == 1:
                # rustfmt keeps a one-element array on one line.
                lines.append(f'pub(super) const GL{n}_{name}: [f64; 1] = '
                             f'[f64::from_bits(0x{to_bits(float(values[0])):016x})];')
                continue
            lines.append(f'pub(super) const GL{n}_{name}: [f64; {m}] = [')
            for v in values:
                lines.append(f'    f64::from_bits(0x{to_bits(float(v)):016x}),')
            lines.append('];')
        if centre is not None:
            lines.append(f'/// The weight of the {n}-point rule\'s centre node, abscissa 0')
            lines.append(f'pub(super) const GL{n}_W0: f64 = f64::from_bits(0x{to_bits(float(centre)):016x});')
    return '\n'.join(lines) + '\n'


def main():
    text = generate()
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != text:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(text)
    print(f'bivariate_normal_nodes: {len(ORDERS) + len(ODD_ORDERS)} rules')


if __name__ == '__main__':
    main()
