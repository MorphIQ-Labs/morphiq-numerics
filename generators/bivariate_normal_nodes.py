#!/usr/bin/env python3
"""The Gauss-Legendre rules of the bivariate normal (docs/bivariate_normal.md).

Writes crates/morphiq-numerics/src/bivariate_normal/tables.rs; with --check,
fails if the committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

For each order n in ORDERS the n/2 positive abscissas and their weights come
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
DPS = 120


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rule(n):
    """Positive abscissas (descending) and weights of the n-point rule."""
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
    assert abs(2 * sum(ws) - 2) < mp.mpf(10) ** (-DPS + 10), n
    return xs, ws


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
    for n in ORDERS:
        xs, ws = rule(n)
        for name, values in (('X', xs), ('W', ws)):
            lines.append(f'/// The {n // 2} positive abscissas of the {n}-point rule'
                         if name == 'X' else f'/// Their weights, summing to 1 over the {n // 2} positive nodes')
            lines.append(f'pub(super) const GL{n}_{name}: [f64; {n // 2}] = [')
            for v in values:
                lines.append(f'    f64::from_bits(0x{to_bits(float(v)):016x}),')
            lines.append('];')
    return '\n'.join(lines) + '\n'


def main():
    text = generate()
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != text:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(text)
    print(f'bivariate_normal_nodes: {len(ORDERS)} rules')


if __name__ == '__main__':
    main()
