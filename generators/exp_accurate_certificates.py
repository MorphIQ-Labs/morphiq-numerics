#!/usr/bin/env python3
"""Writes the accurate path's Gappa certificates (docs/exp.md, section 6), one
per Horner level, so each stays small for Gappa.

The series is H_13 = 1, H_i = 1 + (r * k_i) * H_(i+1) for i = 12..1, in
128-bit significand arithmetic (Q128), against the exact X_i = 1 + (r/i) X_(i+1).
Level i proves |H_i - X_i| <= E_i from |H_(i+1) - X_(i+1)| <= E_(i+1); the
bounds E_i are computed here with a margin and written into the certificates as
literals, so Gappa checks each one. formal/exp/accurate_y.g then bounds
Y = T_j * H_1 against T_j * X_1.

Each Q128 operation is modelled by its contract (docs/exp.md, section 6):
multiplication relative error in [-2^-127, 0]; addition absolute error at most
2^-126 * max(|a|, |b|), here max = 1. k_i = 1/i and T_j carry relative error
below 2^-127 (generators/exp_constants.py).

With --check, fails if the committed certificates differ from a fresh
generation. Pure Python.
"""
from fractions import Fraction
import math
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/exp'
A = Fraction(27078, 10_000_000)  # |r| <= 0.0027078, slightly above the bound
X_RANGE = (Fraction(99, 100), Fraction(101, 100))  # every partial series X_i


def up(v):
    """An upper bound on v, as a power of two times a small integer: m * 2^-e,
    with m < 2^10, at least 1% above v."""
    v = v * Fraction(101, 100)
    e = -math.floor(math.log2(v)) + 9
    m = math.ceil(v * 2**e)
    return m, e


def literal(m, e):
    return f'{m}b-{e}'


def level(i, prev):
    lines = [
        f'# Level {i} of the accurate path\'s series (generators/exp_accurate_certificates.py).',
        '',
        'Hn = Xn + En;',
        f'b = ((r * ((1 / {i}) * (1 + k))) * (1 + ma)) * Hn * (1 + mb);',
        'H = 1 + b + s;',
        f'X = 1 + (r / {i}) * Xn;',
        '',
        '{ r in [-0.0027078, 0.0027078] /\\ Xn in [0.99, 1.01]',
        f'  /\\ En in [-{prev}, {prev}]',
        '  /\\ k in [-1b-127, 1b-127] /\\ ma in [-1b-127, 0] /\\ mb in [-1b-127, 0]',
        '  /\\ s in [-1b-126, 1b-126]',
        '  -> H - X in [-{E}, {E}] }',
        '',
        f'H - X -> (r / {i}) * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s;',
    ]
    return lines


def generate():
    files = {}
    e_prev = Fraction(0)
    for i in range(12, 0, -1):
        h_max = X_RANGE[1] + e_prev
        e_i = A / i * (e_prev + h_max * 3 * Fraction(1, 2**127)) + Fraction(1, 2**126)
        m, e = up(e_i)
        bound = literal(m, e)
        prev = '0' if e_prev == 0 else literal(*up_prev)
        text = '\n'.join(level(i, prev)).replace('{E}', bound) + '\n'
        files[f'accurate_level_{i:02}.g'] = text
        e_prev, up_prev = Fraction(m, 2**e), (m, e)
    files['accurate_y.g'] = '\n'.join([
        '# The accurate path\'s result Y = T_j * H_1 against T_j * X_1',
        '# (generators/exp_accurate_certificates.py).',
        '',
        'H1 = X1 + E1;',
        'Y = (Tj * (1 + eT)) * H1 * (1 + mY);',
        '',
        '{ Tj in [1, 2] /\\ X1 in [0.997, 1.003] /\\ eT in [-1b-127, 1b-127] /\\ mY in [-1b-127, 0]',
        f'  /\\ E1 in [-{literal(*up_prev)}, {literal(*up_prev)}]',
        '  -> (Y - Tj * X1) / (Tj * X1) in [-1b-124, 1b-124] }',
        '',
        '(Y - Tj * X1) / (Tj * X1) -> (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1 { Tj <> 0, X1 <> 0 };',
    ]) + '\n'
    return files


def main():
    files = generate()
    check = '--check' in sys.argv[1:]
    for name, text in files.items():
        path = DIR / name
        if check:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.write_text(text)


if __name__ == '__main__':
    main()
