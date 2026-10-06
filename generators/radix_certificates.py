#!/usr/bin/env python3
"""Writes the Gappa certificates of exp2, log2 and log10 (docs/exp2.md,
docs/log2.md) into formal/exp2 and formal/log2.

No number in a certificate is typed by hand: the constants' errors come from
generators/radix_constants.py, the ratio bound of log2 from an interval
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
import radix_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DW_ADD = '776b-114'  # 3u^2/(1 - 4u), widened (docs/double-word.md)
DW_MUL = '5b-106'    # 5u^2 (docs/double-word.md)
LN_FAST = '1b-64'    # ln's fast path, by case (formal/ln/fast_*.g)
LN_ACCURATE = '1b-123'  # ln's accurate path (formal/ln/accurate_sum_*.g)
FAST = '1b-63'       # eps_1 of log2 and log10
ACCURATE = '1b-122'  # the accurate paths of log2 and log10
REDUCTION = '1b-113'  # exp2's r ln 2: exp's reduction budget (formal/exp/fast.g)


def frac(v):
    man, exp = mpmath.mpf(v).man_exp
    return Fraction(int(man)) * Fraction(2) ** int(exp)


def up(v):
    """A literal m * 2^-e, m < 2^10, at least 1% above |v|."""
    v = abs(frac(v) if not isinstance(v, Fraction) else v) * Fraction(101, 100)
    e = -math.floor(math.log2(v)) + 9
    return f'{math.ceil(v * 2**e)}b-{e}'


def sym(name, literal):
    return f'{name} in [-{literal}, {literal}]'


def kw_bound():
    """max |w / (E + w)| for E != 0, w = log2 y, y in ln's reduced range
    [0.70703125, 1.4140625], widened by 2^-52 as for ln; enclosed with
    mpmath.iv. |E| = 1 attains it: |E + w| only grows with |E|."""
    iv = mpmath.iv
    iv.prec = 128
    w = iv.log(iv.mpf([mpmath.mpf('0.70703125') - mpmath.mpf(2) ** -52,
                       mpmath.mpf('1.4140625') + mpmath.mpf(2) ** -52])) / iv.log(2)
    worst = 0
    for e in (1, -1):
        r = w / (e + w)
        worst = max(worst, abs(mpmath.mp.make_mpf(r._mpi_[0])), abs(mpmath.mp.make_mpf(r._mpi_[1])))
    return worst


def generate():
    mpmath.mp.prec = 600
    d = radix_constants.derive()
    ln2 = mpmath.log(2)
    files = {}
    files['exp2/reduction.g'] = f'''# exp2's reduced argument (docs/exp2.md, section 3): r ln 2 as the double-word
# (p, v) against the exact r ln 2, for every binary64 |r| <= 2^-8.
# Written by generators/radix_certificates.py.
#
#   (p, e) = two_prod(r, H), exact: p + e = r H
#   v = RN(e + RN(r Lo));  (r_hi, r_lo) = two_sum(p, v), exact
# with H = RN(ln 2), Lo = RN(ln 2 - H), and ln 2 = H + Lo + d.

@rnd = float<ieee_64, ne>;

H = {d["ln2_hi"].hex()};
Lo = {d["ln2_lo"].hex()};

r = rnd(r_);
p = rnd(r * H);
e = r * H - p;
u rnd= r * Lo;
v rnd= e + u;
R = r * (H + Lo + dl);

{{ r in [-1b-8, 1b-8] /\\ {sym('dl', up(d['ln2_err'] * ln2))}
  -> (p + v) - R in [-{REDUCTION}, {REDUCTION}] }}

(p + v) - R -> (v - (e + u)) + (u - r * Lo) - r * dl;
'''
    kw = up(kw_bound())
    c2 = up(d['inv_ln2']['err'])
    files['log2/fast_log2.g'] = f'''# log2's fast path (docs/log2.md, section 3), relative to log2 x = E + w,
# w = log2 y = (ln y)/ln 2. Written by generators/radix_certificates.py.
#   S = ln y (1 + eS): ln's fast path for ln y (formal/ln/fast_a.g, fast_b.g with E = 0)
#   C = (1/ln 2)(1 + eC): the double-word constant (generated)
#   W = S.mul(C), relative error em: mul, 5u^2
#   E = 0: the result is W.  E != 0: Y = E.add(W), relative error ea.
# kw = w/(E + w) and ke = E/(E + w) = 1 - kw, |kw| bounded by enclosure.

ke = 1 - kw;
Y = (ke + kw * (1 + eS) * (1 + eC) * (1 + em)) * (1 + ea);
Y0 = (1 + eS) * (1 + eC) * (1 + em);

{{ {sym('kw', kw)} /\\ {sym('eS', LN_FAST)} /\\ {sym('eC', c2)}
  /\\ {sym('em', DW_MUL)} /\\ {sym('ea', DW_ADD)}
  -> Y - 1 in [-{FAST}, {FAST}] /\\ Y0 - 1 in [-{FAST}, {FAST}] }}

Y - 1 -> kw * ((1 + eS) * (1 + eC) * (1 + em) - 1) * (1 + ea) + ea;
'''
    q2 = up(d['inv_ln2']['qerr'])
    files['log2/accurate_log2.g'] = f'''# log2's accurate path (docs/log2.md, section 4) in Q128, relative to
# log2 x = E + w. Written by generators/radix_certificates.py.
#   A = ln y (1 + eA): ln's accurate path for ln y (formal/ln/accurate_sum_a.g, _b.g)
#   C = (1/ln 2)(1 + eC), and the product truncated, m in [-2^-127, 0]
#   E = 0: the result is A C.  E != 0: E converts exactly, and the addition
#   errs by at most 2^-126 max(|E|, |w|) (1 + 2^-120), over |E + w|: s.

ke = 1 - kw;
Y = ke + kw * (1 + eA) * (1 + eC) * (1 + m) + s;
Y0 = (1 + eA) * (1 + eC) * (1 + m);

{{ {sym('kw', kw)} /\\ {sym('eA', LN_ACCURATE)} /\\ {sym('eC', q2)}
  /\\ m in [-1b-127, 0] /\\ {sym('s', up(Fraction(2, 2**127) * (1 + frac(kw_bound()))))}
  -> Y - 1 in [-{ACCURATE}, {ACCURATE}] /\\ Y0 - 1 in [-{ACCURATE}, {ACCURATE}] }}

Y - 1 -> kw * ((1 + eA) * (1 + eC) * (1 + m) - 1) + s;
'''
    c10 = up(d['inv_ln10']['err'])
    q10 = up(d['inv_ln10']['qerr'])
    files['log2/fast_log10.g'] = f'''# log10's fast path (docs/log2.md, section 5): ln's fast result
# ln x (1 + eL) (formal/ln/fast_a.g, _b.g, _c.g), times the double-word
# 1/ln 10 (1 + eC), by mul (5u^2). Written by generators/radix_certificates.py.

Y = (1 + eL) * (1 + eC) * (1 + em);

{{ {sym('eL', LN_FAST)} /\\ {sym('eC', c10)} /\\ {sym('em', DW_MUL)}
  -> Y - 1 in [-{FAST}, {FAST}] }}
'''
    files['log2/accurate_log10.g'] = f'''# log10's accurate path (docs/log2.md, section 5): ln's accurate result
# ln x (1 + eA) (formal/ln/accurate_sum_*.g) times 1/ln 10 in Q128 (1 + eC),
# the product truncated. Written by generators/radix_certificates.py.

Y = (1 + eA) * (1 + eC) * (1 + m);

{{ {sym('eA', LN_ACCURATE)} /\\ {sym('eC', q10)} /\\ m in [-1b-127, 0]
  -> Y - 1 in [-{ACCURATE}, {ACCURATE}] }}
'''
    return files


def main():
    files = generate()
    for name, text in files.items():
        path = ROOT / 'formal' / name
        if '--check' in sys.argv[1:]:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
