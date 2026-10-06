#!/usr/bin/env python3
"""Reference Box-Muller pairs: an implementation of the specification in
docs/random.md separate from the Rust crate.

  u1 = unit_open(w1) = (2 (w1 >> 12) + 1) 2^-53
  u2 = unit_closed_open(w2) = (w2 >> 11) 2^-53
  rho = RN(sqrt(-2 RN(ln u1))), theta = RN(RN(2 pi) u2)
  (RN(rho RN(cos theta)), RN(rho RN(sin theta)))

ln, sqrt, sin and cos are correctly rounded by the interval oracle in
generators/oracle; the words come from generators/random_streams_reference.py's
streams; the products are Python's binary64 multiplications, rounded to nearest
by IEEE 754.

Writes crates/reference/fixtures/box_muller.json; with --check, fails if the
committed fixture differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

The cases:
- the first 256 pairs of SplitMix64 and of xoshiro256++ from six seeds;
- edge words: u1 at its least and greatest values and at 1/2, against u2 at 0,
  at the quarter turns and their neighbours, and at its greatest value.
"""
import json
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import correctly_rounded, to_bits
from random_streams_reference import SEEDS, splitmix64, xoshiro256pp

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/box_muller.json'
MASK = (1 << 64) - 1
PAIRS = 256


def tau_rn():
    with mpmath.workprec(200):
        return float(2 * mpmath.pi)


def pair(w1, w2):
    u1 = (2 * (w1 >> 12) + 1) * 2.0 ** -53
    u2 = (w2 >> 11) * 2.0 ** -53
    rho = correctly_rounded(iv.sqrt, -2.0 * correctly_rounded(iv.log, u1))
    theta = tau_rn() * u2
    if theta == 0.0:
        s, c = 0.0, 1.0
    else:
        s, c = correctly_rounded(iv.sin, theta), correctly_rounded(iv.cos, theta)
    return rho * c, rho * s


def entry(w1, w2):
    z0, z1 = pair(w1, w2)
    return {'w1': f'{w1:016x}', 'w2': f'{w2:016x}', 'z0': f'{to_bits(z0):016x}', 'z1': f'{to_bits(z1):016x}'}


def stream(words):
    return [entry(next(words), next(words)) for _ in range(PAIRS)]


def edge_cases():
    w1s = [0, MASK, 1 << 63, (1 << 63) - 1]
    w2s = [0, 1 << 11, MASK]
    for quarter in (1, 2, 3):
        w = quarter << 62
        w2s += [w - (1 << 11), w, w + (1 << 11)]
    return [entry(w1, w2) for w1 in w1s for w2 in w2s]


def document():
    return {
        'generator': 'generators/box_muller_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike at two precisions',
        'rounding': 'to nearest, ties to even',
        'tau': f'{to_bits(tau_rn()):016x}',
        'sources': ['Box and Muller, Annals of Mathematical Statistics 29(2), 1958'],
        'edges': edge_cases(),
        'splitmix64': {f'{seed:016x}': stream(splitmix64(seed)) for seed in SEEDS},
        'xoshiro256pp': {f'{seed:016x}': stream(xoshiro256pp(seed)) for seed in SEEDS},
    }


def main():
    data = json.dumps(document(), indent=1) + '\n'
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != data:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        return
    OUTPUT.write_text(data)


if __name__ == '__main__':
    main()
