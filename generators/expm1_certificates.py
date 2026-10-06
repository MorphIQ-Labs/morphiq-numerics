#!/usr/bin/env python3
"""Writes the Gappa certificates of expm1 (docs/expm1.md) into formal/expm1.

No number in a certificate is typed by hand: the polynomial and its bound come
from generators/expm1_poly.out, the series degree and reciprocals from
generators/expm1_constants.py, the cancellation ratio from an interval
enclosure here, and every other hypothesis is a bound certified elsewhere
(named where it is used), widened by at least 1% (`up`).

With --check, fails if the committed certificates differ from a fresh
generation. Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

import mpmath

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import expm1_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/expm1'
A = expm1_constants.A
A_LIT = '0.0312501'
X_MIN = '1b-54'  # the small path's least |x| (section 1)
U = Fraction(1, 2**127)
DW_ADD = '776b-114'  # 3u^2/(1 - 4u), widened (docs/double-word.md)
TAIL = '1b-50'
POLY = '13b-66'  # 2^-62.3: the tail's 2^-50 weighted by x^2/6 <= 2^-12.6
EXP_FAST = '1b-69'  # exp's fast path at the reduced argument (formal/exp/fast.g)
EXP_ACCURATE = '1097b-134'  # exp's accurate path, below 2^-123.9 (docs/exp.md, section 6)
FAST = '1b-62'  # expm1's eps_1 (docs/expm1.md, section 6)
ACCURATE_SMALL = '1b-123'
ACCURATE_GENERAL = '1b-118'


def frac(v):
    if isinstance(v, Fraction):
        return v
    man, exp = mpmath.mpf(v).man_exp
    return Fraction(int(man)) * Fraction(2) ** int(exp)


def up(v):
    v = abs(frac(v)) * Fraction(101, 100)
    e = -math.floor(math.log2(v)) + 9
    return f'{math.ceil(v * 2**e)}b-{e}'


def value(literal):
    m, e = literal.split('b-')
    return Fraction(int(m), 2 ** int(e))


def hex_fraction(text):
    mantissa, exponent = text.lstrip('-')[2:].split('p')
    whole, _, fraction = mantissa.partition('.')
    return Fraction(int(whole + fraction, 16)) * Fraction(2) ** (int(exponent) - 4 * len(fraction))


def sym(name, literal):
    return f'{name} in [-{literal}, {literal}]'


def kq_bound():
    """max |e^x / (e^x - 1)| over |x| >= 2^-5: at |x| = 2^-5, since the ratio's
    magnitude decreases as |x| grows on either side; enclosed with mpmath.iv."""
    iv = mpmath.iv
    iv.prec = 128
    worst = 0
    for x in (mpmath.mpf(2) ** -5, -mpmath.mpf(2) ** -5):
        q = iv.exp(iv.mpf(x))
        r = q / (q - 1)
        worst = max(worst, abs(mpmath.mp.make_mpf(r._mpi_[0])), abs(mpmath.mp.make_mpf(r._mpi_[1])))
    return frac(worst)


def coefficients():
    values = dict(line.split() for line in expm1_constants.POLY.read_text().split('\n') if line.strip())
    return '\n'.join(f'c{k} = {values[f"c{k}"]};' for k in range(3, 10)), values['relative_error_bound']


def horner(var):
    s = 'c9'
    for k in range(8, 2, -1):
        s = f'(c{k} + {var} * {s})'
    return s


def small_fast():
    c, bound = coefficients()
    rho = up(hex_fraction(bound))
    tail = f'''# expm1's small-argument tail (docs/expm1.md, section 3): with x a binary64,
# {X_MIN} <= |x| <= {A_LIT},
#   w = c3 + x*(c4 + ... + x*c9),  x3 = RN(x * RN(x^2)),  t = RN(x3 * w)
# rounded to binary64, nearest-even, against x^3 W(x) evaluated exactly.
# Written by generators/expm1_certificates.py.

@rnd = float<ieee_64, ne>;

{c}

x = rnd(x_);

w8 rnd= c8 + x * c9;
w7 rnd= c7 + x * w8;
w6 rnd= c6 + x * w7;
w5 rnd= c5 + x * w6;
w4 rnd= c4 + x * w5;
w  rnd= c3 + x * w4;
sh rnd= x * x;
x3 rnd= x * sh;
t  rnd= x3 * w;

W = {horner('x')};
T = x * x * x * W;

{{ |x| in [{X_MIN}, {A_LIT}] -> (t - T) / T in [-{TAIL}, {TAIL}] }}

(t - T) / T -> (1 + (x3 - x * x * x) / (x * x * x)) * (1 + (w - W) / W) * (1 + (t - x3 * w) / (x3 * w)) - 1;
(x3 - x * x * x) / (x * x * x) -> (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1;
'''
    p = f'''# expm1's small-argument result (docs/expm1.md, section 3):
#   P = add_f64(add(x, x^2/2 as a double-word), t)
# against e^x - 1, relative. Written by generators/expm1_certificates.py.
#   t = T (1 + et), |et| <= {TAIL}                (formal/expm1/tail.g)
#   e^x - 1 = x + x^2/2 + T + a, |a| <= rho |T|, rho = {bound}
#     (generators/expm1_poly.sollya, supnorm, relative)
#   x^2/2 is exact: x^2 = s_hi + s_lo by two_prod, and halving is exact.
#   the double-word additions' relative bounds (docs/double-word.md):
#   add 3u^2/(1 - 4u) (d1), add_f64 2u^2 (d2).

{c}

W = {horner('x')};
T = x * x * x * W;
t = T * (1 + et);
B = x * x / 2;
P1 = (x + B) * (1 + d1);
P = (P1 + t) * (1 + d2);
L = x + B + T * (1 + al);

{{ |x| in [{X_MIN}, {A_LIT}] /\\ {sym('et', TAIL)} /\\ {sym('al', rho)}
  /\\ {sym('d1', DW_ADD)} /\\ {sym('d2', '1b-105')}
  -> (P - L) / L in [-{POLY}, {POLY}] }}

(P - L) / L -> ((P - L) / x) / (L / x);
L / x -> 1 + x / 2 + x * x * W * (1 + al);
(P - L) / x -> x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2;
'''
    return {'tail.g': tail, 'p.g': p}


def small_accurate():
    files = {}
    d = expm1_constants.DEGREE
    # H_(d+2) = 1 exactly; H_m = 1 + (x (1/m)) H_(m+1), m = d+1 .. 2.
    e_prev, prev = Fraction(0), '0'
    for m in range(d + 1, 1, -1):
        # X_(m+1) = sum_n x^n m!/(m+n)!: within 1 +- A/(m+1) / (1 - A).
        spread = A / (m + 1) / (1 - A)
        x_lo, x_hi = 1 - spread, 1 + spread
        g_max = x_hi + e_prev
        bound = up(A / m * (e_prev + g_max * 3 * U) + 2 * U)
        files[f'accurate_level_{m:02}.g'] = f'''# Level {m} of expm1's small-argument series in Q128 (docs/expm1.md, section 4):
# H_{m} = 1 + (x (1/{m})) H_{m + 1} against X_{m} = 1 + (x/{m}) X_{m + 1}, given
# |H_{m + 1} - X_{m + 1}| <= {prev}. Written by generators/expm1_certificates.py.

Hn = Xn + En;
b = ((x * ((1 / {m}) * (1 + kk))) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + s;
X = 1 + (x / {m}) * Xn;

{{ x in [-{A_LIT}, {A_LIT}] /\\ Xn in [{float(x_lo * Fraction(99, 100)):.9f}, {float(x_hi * Fraction(101, 100)):.9f}]
  /\\ {sym('En', prev)}
  /\\ kk in [-1b-127, 1b-127] /\\ ma in [-1b-127, 0] /\\ mb in [-1b-127, 0] /\\ s in [-1b-126, 1b-126]
  -> H - X in [-{bound}, {bound}] }}

H - X -> (x / {m}) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s;
'''
        prev, e_prev = bound, value(bound)
    # G = (e^x - 1)/x = X_2 + truncation, the first omitted term below
    # A^(d+1)/(d+2)!.
    e2 = up(e_prev + A ** (d + 1) / math.factorial(d + 2))
    spread = A / 2 / (1 - A)
    files['accurate_small.g'] = f'''# expm1's small-argument accurate result (docs/expm1.md, section 4):
# x H_2 in Q128 against e^x - 1 = x G, G = (e^x - 1)/x, relative.
# |H_2 - G| <= E2: the levels and the truncation. The product is truncated.
# Written by generators/expm1_certificates.py.

Y = (G + E2) * (1 + m) / G;

{{ G in [{float((1 - spread) * Fraction(99, 100)):.9f}, {float((1 + spread) * Fraction(101, 100)):.9f}] /\\ {sym('E2', e2)} /\\ m in [-1b-127, 0]
  -> Y - 1 in [-{ACCURATE_SMALL}, {ACCURATE_SMALL}] }}

Y - 1 -> E2 / G + (1 + E2 / G) * m;
'''
    return files


def general():
    kq = up(kq_bound())
    s_rel = up(Fraction(2, 2**127) * (kq_bound() + 1))
    fast = f'''# expm1's fast result for |x| >= 2^-5 (docs/expm1.md, section 5):
#   M = (Y.add_f64(-2^-k)) 2^k, Y = 2^(j/128) e^R (1 + eY) from exp's fast path
# against e^x - 1 = 2^k (2^(j/128) e^R - 2^-k), relative. With
# kq = e^x/(e^x - 1), |kq| <= KQ (enclosed at |x| = 2^-5), the relative error
# is kq eY (1 + ea) + ea. The scaling by 2^k is exact.
# Written by generators/expm1_certificates.py.

M = (1 + kq * eY) * (1 + ea);

{{ {sym('kq', kq)} /\\ {sym('eY', EXP_FAST)} /\\ {sym('ea', '1b-105')}
  -> M - 1 in [-{FAST}, {FAST}] }}

M - 1 -> kq * eY * (1 + ea) + ea;
'''
    accurate = f'''# expm1's accurate result for |x| >= 2^-5 (docs/expm1.md, section 5):
# V = e^x (1 + eV) from exp's accurate path, then V - 1 in Q128 with absolute
# error s <= 2^-126 max(V, 1). Relative to e^x - 1: kq eV + s/(e^x - 1), and
# max(V, 1)/|e^x - 1| <= max(|kq| (1 + eV), |kq - 1|) <= KQ + 1.
# Written by generators/expm1_certificates.py.

M = 1 + kq * eV + sr;

{{ {sym('kq', kq)} /\\ {sym('eV', EXP_ACCURATE)} /\\ {sym('sr', s_rel)}
  -> M - 1 in [-{ACCURATE_GENERAL}, {ACCURATE_GENERAL}] }}
'''
    return {'fast_general.g': fast, 'accurate_general.g': accurate}


def generate():
    files = {}
    files.update(small_fast())
    files.update(small_accurate())
    files.update(general())
    return files


def main():
    files = generate()
    check = '--check' in sys.argv[1:]
    if check:
        present = {p.name for p in DIR.glob('*.g')}
        if present != set(files):
            sys.exit(f'formal/expm1 holds {sorted(present ^ set(files))} unexpectedly')
    for name, text in files.items():
        path = DIR / name
        if check:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
