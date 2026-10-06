#!/usr/bin/env python3
"""Writes the Gappa certificates of sin and cos (docs/sin_cos.md) into
formal/trig.

No number in a certificate is typed by hand: the polynomials and their bounds
come from generators/trig_poly.out, the table's error, the series degrees and
the ratios from generators/trig_constants.py, and every other hypothesis is a
bound certified elsewhere (named where it is used), widened by at least 1%
(`up`).

With --check, fails if the committed certificates differ from a fresh
generation. Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

import mpmath

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import trig_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/trig'
T_LIT = '0.0078126'
T_MIN = '1b-320'  # t is 0 or at least 2^-317 in magnitude (section 4)
T_SPLIT = '1b-60'  # above it nothing underflows; below it t = r_lo (section 4)
DW_ADD = '776b-114'  # add and sub: 3u^2/(1 - 4u), widened (docs/double-word.md)
DW_MUL = '5b-106'    # mul: 5u^2 (docs/double-word.md)
TAIL = '1b-50'
SIN_T = '1b-65'
COS_T = '1b-65'
REDUCTION_FAST = '1b-104'  # r's double-word against Q256's r, as an effect on the value
FAST = '1b-62'
LEVEL_U = Fraction(1, 2**255)
SERIES = '1b-240'
QUARTER_PI_SQ = Fraction(61685, 100000)  # (pi/4)^2 < 0.61685


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


def constants(values, prefix):
    return '\n'.join(f'{prefix}{k} = {values[f"{prefix}{k}"]};' for k in range(3))


def tails(values):
    """The two tail evaluations in binary64, against the polynomials evaluated
    exactly at t_hi."""
    sin_tail = f'''# The fast path's sine tail (docs/sin_cos.md, section 4): with t_hi a binary64,
# {T_SPLIT} <= |t_hi| <= {T_LIT},
#   u = RN(t_hi^2), ps = s0 + u (s1 + u s2), tail = RN(RN(t_hi u) ps)
# against t_hi^3 Ps(t_hi^2). Written by generators/trig_certificates.py.

@rnd = float<ieee_64, ne>;

{constants(values, 's')}

th = rnd(th_);
uh rnd= th * th;
p2 rnd= s1 + uh * s2;
ps rnd= s0 + uh * p2;
a3 rnd= th * uh;
tail rnd= a3 * ps;
P = s0 + th * th * (s1 + th * th * s2);
T = th * th * th * P;

{{ |th| in [{T_SPLIT}, {T_LIT}] -> (tail - T) / T in [-{TAIL}, {TAIL}] }}

(tail - T) / T -> (1 + (a3 - th * th * th) / (th * th * th)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1;
(a3 - th * th * th) / (th * th * th) -> (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1;
'''
    cos_tail = f'''# The fast path's cosine tail (docs/sin_cos.md, section 4): with t_hi a
# binary64, {T_SPLIT} <= |t_hi| <= {T_LIT},
#   u = RN(t_hi^2), pc = c0 + u (c1 + u c2), tail = RN(RN(u u) pc)
# against t_hi^4 Pc(t_hi^2). Written by generators/trig_certificates.py.

@rnd = float<ieee_64, ne>;

{constants(values, 'c')}

th = rnd(th_);
uh rnd= th * th;
p2 rnd= c1 + uh * c2;
pc rnd= c0 + uh * p2;
a4 rnd= uh * uh;
tail rnd= a4 * pc;
P = c0 + th * th * (c1 + th * th * c2);
T = th * th * th * th * P;

{{ |th| in [{T_SPLIT}, {T_LIT}] -> (tail - T) / T in [-{TAIL}, {TAIL}] }}

(tail - T) / T -> (1 + (a4 - th * th * th * th) / (th * th * th * th)) * (1 + (pc - P) / P) * (1 + (tail - a4 * pc) / (a4 * pc)) - 1;
(a4 - th * th * th * th) / (th * th * th * th) -> (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1;
'''
    return {'sin_tail.g': sin_tail, 'cos_tail.g': cos_tail}


def compositions(values, tiny):
    """sin t and cos t - 1 from their tails. Above 2^-60 the tails' errors are
    certified (formal/trig/*_tail.g); below, where t = r_lo and t^4 may
    underflow, a tail is only known to lie between 0 and 3 times its value,
    which still contributes below 2^-118 relative."""
    rho_s = up(hex_fraction(values['sin_error_bound']))
    rho_c = up(hex_fraction(values['cos_error_bound']))
    lo, hi = (T_MIN, T_SPLIT) if tiny else (T_SPLIT, T_LIT)
    tail = '[-1, 2]' if tiny else f'[-{TAIL}, {TAIL}]'
    note = ('# For |t_hi| below 2^-60: t = r_lo, and a tail may underflow; it lies\n'
            '# within [0, 3] times its value (et in [-1, 2]).\n') if tiny else ''
    sin_t = f'''{note}# sin t for the double-word t = t_hi + t_lo, |t_lo| <= 2^-53 |t_hi|
# (docs/sin_cos.md, section 4): SN = add_f64(t, tail) against sin t, relative.
# Written by generators/trig_certificates.py.
#   tail = t_hi^3 Ps(t_hi^2) (1 + et)              (formal/trig/sin_tail.g)
#   sin t = t + t^3 Ps(t^2) (1 + al), |al| <= rho   (generators/trig_poly.sollya)
#   add_f64: 2u^2 (docs/double-word.md)

{constants(values, 's')}

t = th * (1 + dl);
Ph = s0 + th * th * (s1 + th * th * s2);
Pt = s0 + t * t * (s1 + t * t * s2);
SN = (t + th * th * th * Ph * (1 + et)) * (1 + d2);
ST = t + t * t * t * Pt * (1 + al);

{{ |th| in [{lo}, {hi}] /\\ {sym('dl', '1b-53')} /\\ et in {tail} /\\ {sym('al', rho_s)}
  /\\ {sym('d2', '1b-105')}
  -> (SN - ST) / ST in [-{SIN_T}, {SIN_T}] }}

(SN - ST) / ST -> ((SN - ST) / th) / (ST / th);
ST / th -> (1 + dl) + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al);
(SN - ST) / th -> (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al));
Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al) ->
  Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1)
  - th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl)));
'''
    cos_t = f'''{note}# cos t - 1 for the double-word t (docs/sin_cos.md, section 4):
#   CM = add_f64(-t_hi^2/2 as an exact double-word, v),
#   v = RN(tail - RN(t_hi t_lo))
# against cos t - 1, relative. Written by generators/trig_certificates.py.
#   tail = t_hi^4 Pc(t_hi^2) (1 + et)                (formal/trig/cos_tail.g)
#   cos t - 1 = -t^2/2 + t^4 Pc(t^2) (1 + al), |al| <= rho
#   t_hi t_lo = t_hi^2 dl, rounded (ec); the subtraction rounded (eu);
#   add_f64: 2u^2.

{constants(values, 'c')}

t = th * (1 + dl);
Ph = c0 + th * th * (c1 + th * th * c2);
Pt = c0 + t * t * (c1 + t * t * c2);
V = (th * th * th * th * Ph * (1 + et) - th * th * dl * (1 + ec)) * (1 + eu);
CM = (-(th * th) / 2 + V) * (1 + d2);
CT = -(t * t) / 2 + t * t * t * t * Pt * (1 + al);

{{ |th| in [{lo}, {hi}] /\\ {sym('dl', '1b-53')} /\\ et in {tail} /\\ {sym('al', rho_c)}
  /\\ {sym('ec', '1b-53')} /\\ {sym('eu', '1b-53')} /\\ {sym('d2', '1b-105')}
  -> (CM - CT) / CT in [-{COS_T}, {COS_T}] }}

(CM - CT) / CT -> ((CM - CT) / (th * th)) / (CT / (th * th));
CT / (th * th) -> -(1 + dl) * (1 + dl) / 2 + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al);
(CM - CT) / (th * th) ->
  th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1)
             - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl))))
  + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2;
'''
    suffix = '_tiny' if tiny else ''
    return {f'sin_t{suffix}.g': sin_t, f'cos_t{suffix}.g': cos_t}


def fast(d):
    k = d['ratios']
    table = up(d['worst'])
    sin = f'''# The fast sin(a + t) (docs/sin_cos.md, section 4):
#   R = S.add(S.mul(CM).add(C.mul(SN)))
# relative to sin(a + t) = S + S (cos t - 1) + C sin t. Written by
# generators/trig_certificates.py. With ks, ka, kb those three terms over
# sin(a + t) (ks + ka + kb = 1; bounds enclosed by generators/trig_constants.py):
#   S, C: the table's double-words, relative error eS, eC (generated)
#   SN, CM: sin t, cos t - 1 (formal/trig/sin_t.g, cos_t.g)
#   m1, m2: mul, 5u^2; a1, a2: add, 3u^2/(1 - 4u)
#   er: r's double-word against Q256's r, as an effect on sin(a + t)

ks = 1 - ka - kb;
X = (1 + eS) * (1 + eCM) * (1 + m1);
Z = (1 + eC) * (1 + eSN) * (1 + m2);
R = (ks * (1 + eS) + (ka * X + kb * Z) * (1 + a1)) * (1 + a2) * (1 + er);

{{ {sym('ka', up(k['ka']))} /\\ {sym('kb', up(k['kb']))} /\\ {sym('eS', table)} /\\ {sym('eC', table)}
  /\\ {sym('eSN', SIN_T)} /\\ {sym('eCM', COS_T)} /\\ {sym('m1', DW_MUL)} /\\ {sym('m2', DW_MUL)}
  /\\ {sym('a1', DW_ADD)} /\\ {sym('a2', DW_ADD)} /\\ {sym('er', REDUCTION_FAST)}
  -> R - 1 in [-{FAST}, {FAST}] }}

R - 1 -> (ks * eS + (ka * (X - 1) + kb * (Z - 1)) * (1 + a1) + (ka + kb) * a1
          + (ks * (1 + eS) + (ka * X + kb * Z) * (1 + a1)) * a2) * (1 + er) + er;
'''
    cos = f'''# The fast cos(a + t) (docs/sin_cos.md, section 4):
#   R = C.add(C.mul(CM).sub(S.mul(SN)))
# relative to cos(a + t) = C + C (cos t - 1) - S sin t, with kc, kca, ksb those
# terms over cos(a + t) (kc + kca - ksb = 1). Written by
# generators/trig_certificates.py; the hypotheses are as for fast_sin.g.

kc = 1 - kca + ksb;
X = (1 + eC) * (1 + eCM) * (1 + m1);
Z = (1 + eS) * (1 + eSN) * (1 + m2);
R = (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * (1 + a2) * (1 + er);

{{ {sym('kca', up(k['kca']))} /\\ {sym('ksb', up(k['ksb']))} /\\ {sym('eS', table)} /\\ {sym('eC', table)}
  /\\ {sym('eSN', SIN_T)} /\\ {sym('eCM', COS_T)} /\\ {sym('m1', DW_MUL)} /\\ {sym('m2', DW_MUL)}
  /\\ {sym('a1', DW_ADD)} /\\ {sym('a2', DW_ADD)} /\\ {sym('er', REDUCTION_FAST)}
  -> R - 1 in [-{FAST}, {FAST}] }}

R - 1 -> (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1
          + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er;
'''
    return {'fast_sin.g': sin, 'fast_cos.g': cos}


def series(name, n_terms, step):
    """The Q256 series levels: H_n = 1 - (s c_n) H_(n+1), H_(N+1) = 1, against
    X_n = 1 - s c_n X_(n+1) at the same s, |s| <= (pi/4)^2."""
    files = {}
    e_prev, prev = Fraction(0), '0'
    for n in range(n_terms, 0, -1):
        c = step(n)
        # X_(n+1) lies within 1 - [0, s c_(n+1)]: alternating, decreasing.
        c_next = step(n + 1)
        x_lo, x_hi = 1 - QUARTER_PI_SQ * c_next, Fraction(1)
        g_max = x_hi + e_prev
        bound = up(QUARTER_PI_SQ * c * (e_prev + g_max * 3 * LEVEL_U) + 2 * LEVEL_U)
        files[f'{name}_level_{n:02}.g'] = f'''# Level {n} of {name}'s Q256 series (docs/sin_cos.md, section 5):
# H_{n} = 1 - (s c) H_{n + 1} against X_{n} = 1 - s c X_{n + 1}, c = {c.numerator}/{c.denominator},
# given |H_{n + 1} - X_{n + 1}| <= {prev}. Written by generators/trig_certificates.py.

Hn = Xn + En;
b = ((s * ({c.numerator} / {c.denominator}) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 - b + sa;
X = 1 - s * ({c.numerator} / {c.denominator}) * Xn;

{{ s in [0, {float(QUARTER_PI_SQ)}] /\\ Xn in [{float(x_lo) * 0.99:.9f}, 1]
  /\\ {sym('En', prev)}
  /\\ kk in [-1b-255, 1b-255] /\\ ma in [-1b-255, 0] /\\ mb in [-1b-255, 0] /\\ sa in [-1b-254, 1b-254]
  -> H - X in [-{bound}, {bound}] }}

H - X -> -(s * ({c.numerator} / {c.denominator})) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
'''
        prev, e_prev = bound, value(bound)
    return files, e_prev


def generate():
    d = trig_constants.derive()
    values = d['values']
    files = {}
    files.update(tails(values))
    files.update(compositions(values, tiny=False))
    files.update(compositions(values, tiny=True))
    files.update(fast(d))
    sin_levels, e_sin = series('sin', d['n_sin'], lambda n: Fraction(1, (2 * n) * (2 * n + 1)))
    cos_levels, e_cos = series('cos', d['n_cos'], lambda n: Fraction(1, (2 * n - 1) * (2 * n)))
    files.update(sin_levels)
    files.update(cos_levels)
    files.update(accurate(d, e_sin, e_cos))
    return files


def accurate(d, e_sin, e_cos):
    """The accurate results end to end (section 5), relative to sin x or cos x
    in the quadrant's form, sin r or cos r of the exact r.
      - r carries the reduction's relative error, at most 2^-199
        (src/trig/tests.rs checks it against 256-bit references); by the mean
        value theorem |sin(r(1 + e)) - sin r| <= |r e|, and over
        sin r >= (sin(pi/4)/(pi/4)) r that is at most 1.1108 |e|; likewise
        |cos(r(1 + e)) - cos r| <= r^2 |e| (1 + |e|), over cos r >= cos(pi/4)
        at most 0.8726 |e|. These enter as dr.
      - s = r^2 is one product, which moves the series by at most
        |s| 2^-255 |H'| <= 2^-256; it enters with the levels' error.
      - The truncation's first omitted term is at most 2^-210, relative."""
    trunc = Fraction(1, 2**210)
    shift = Fraction(1, 2**256)
    files = {}
    for name, e_levels, x_lo, ratio in (
        ('sin', e_sin, Fraction(9, 10), Fraction(11108, 10000)),
        ('cos', e_cos, Fraction(7, 10), Fraction(8726, 10000)),
    ):
        h = up(e_levels + shift + trunc)
        dr = up(Fraction(1, 2**199) * ratio)
        product = '(1 + m1) * ' if name == 'sin' else ''
        product_hyp = ' /\\ m1 in [-1b-255, 0]' if name == 'sin' else ''
        files[f'accurate_{name}.g'] = f'''# {name}'s accurate result (docs/sin_cos.md, section 5) relative to {name} of the
# exact r. H_1 is within E1 of the exact series value X1 ({'sin r / r' if name == 'sin' else 'cos r'}), the levels'
# error, the product s = r^2 and the truncation together; {'the product r H_1 is\n# truncated (m1); ' if name == 'sin' else ''}the reduction's error enters as dr. Written by
# generators/trig_certificates.py.

Y = {product}(1 + E1 / X1) * (1 + dr);

{{ X1 in [{float(x_lo)}, 1] /\\ {sym('E1', h)} /\\ {sym('dr', dr)}{product_hyp}
  -> Y - 1 in [-1b-198, 1b-198] }}
'''
    return files


def main():
    files = generate()
    check = '--check' in sys.argv[1:]
    if check:
        present = {p.name for p in DIR.glob('*.g')}
        if present != set(files):
            sys.exit(f'formal/trig holds {sorted(present ^ set(files))} unexpectedly')
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
