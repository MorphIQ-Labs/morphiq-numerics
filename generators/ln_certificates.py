#!/usr/bin/env python3
"""Writes every Gappa certificate of ln and ln_1p (docs/ln.md) into formal/ln.

No number in a certificate is typed by hand. The polynomial and its
approximation bound come from generators/ln_poly.out (generators/ln_poly.sollya);
the table errors, the error of E ln 2 and the ratios of each reduction case come
from generators/ln_constants.py; the remaining inputs are derived below. Each
hypothesis is a derived bound widened by at least 1% (`up`), and each goal is
a target Gappa must prove: a goal a later certificate assumes is passed on as
that certificate's hypothesis, so the chain is checked link by link.

With --check, fails if the committed certificates differ from a fresh
generation. Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

import mpmath

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import ln_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/ln'
Z = ln_constants.Z_BOUND  # |z| <= 0.0078126 (section 3)
Z_MIN = '1b-64'  # z is zero or at least 2^-63 in magnitude (section 3)
U = Fraction(1, 2**127)
DEGREE = ln_constants.DEGREE  # the accurate path's series (section 6)

# The goals: each is proved by its certificate and assumed by the next.
TAIL = '1b-50'  # formal/ln/tail.g
POLY = '3b-66'  # formal/ln/p.g: dP, relative to ln(1 + z)
FAST = '1b-64'  # formal/ln/fast_{a,b,c}.g: ln's fast path
FAST_LN_1P = '1b-63'  # formal/ln/fast_ln_1p.g: ln_1p's; eps_1 for both (section 5)
ACCURATE = '1b-123'  # formal/ln/accurate_sum_*.g


def frac(v):
    """An mpf or Fraction as a Fraction, exactly."""
    if isinstance(v, Fraction):
        return v
    man, exp = mpmath.mpf(v).man_exp
    return Fraction(int(man)) * Fraction(2) ** int(exp)


def up(v):
    """A literal m * 2^-e, m < 2^10, at least 1% above |v|."""
    v = abs(frac(v)) * Fraction(101, 100)
    e = -math.floor(math.log2(v)) + 9
    return f'{math.ceil(v * 2**e)}b-{e}'


def hex_fraction(text):
    """A hexadecimal literal as Sollya prints it (0x1.08...p-54), exactly."""
    sign = -1 if text.startswith('-') else 1
    mantissa, exponent = text.lstrip('-')[2:].split('p')
    whole, _, fraction = mantissa.partition('.')
    digits = int(whole + fraction, 16)
    return sign * Fraction(digits) * Fraction(2) ** (int(exponent) - 4 * len(fraction))


def value(literal):
    m, e = literal.split('b-')
    return Fraction(int(m), 2 ** int(e))


def sym(name, literal):
    return f'{name} in [-{literal}, {literal}]'


def coefficients(d):
    values = dict(line.split() for line in ln_constants.POLY.read_text().split('\n') if line.strip())
    return '\n'.join(f'c{k} = {values[f"c{k}"]};' for k in range(3, 10))


def horner(var):
    s = 'c9'
    for k in range(8, 2, -1):
        s = f'(c{k} + {var} * {s})'
    return s


def tail(d):
    return f'''# The fast path's cubic tail for ln(1 + z) (docs/ln.md, section 4): with z_hi
# a binary64, {Z_MIN} <= |z_hi| <= 0.0078126,
#   w = c3 + z_hi*(c4 + ... + z_hi*c9),  z3 = RN(z_hi * RN(z_hi^2)),  t = RN(z3 * w)
# rounded to binary64, nearest-even, against z_hi^3 * W(z_hi) evaluated exactly.
# Written by generators/ln_certificates.py.

@rnd = float<ieee_64, ne>;

{coefficients(d)}

zh = rnd(zh_);

w8 rnd= c8 + zh * c9;
w7 rnd= c7 + zh * w8;
w6 rnd= c6 + zh * w7;
w5 rnd= c5 + zh * w6;
w4 rnd= c4 + zh * w5;
w  rnd= c3 + zh * w4;
sh rnd= zh * zh;
z3 rnd= zh * sh;
t  rnd= z3 * w;

W = {horner('zh')};
T = zh * zh * zh * W;

{{ |zh| in [{Z_MIN}, 0.0078126] -> (t - T) / T in [-{TAIL}, {TAIL}] }}

# t / T = (1 + e_z3) (1 + e_w) (1 + e_t), the relative errors of z3, w and the
# last product.
(t - T) / T -> (1 + (z3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (w - W) / W) * (1 + (t - z3 * w) / (z3 * w)) - 1;
(z3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1;
'''


def poly(d):
    terms = []
    for j in range(1, 7):
        mon = ' + '.join(('*'.join(['z'] * i + ['zh'] * (j - 1 - i)) or '1') for i in range(j))
        terms.append(f'c{j + 3} * ({mon})')
    rho = up(hex_fraction(d['poly_bound']))
    dw_add = up(Fraction(3, 2**106) / (1 - Fraction(4, 2**53)))
    return f'''# The fast path's ln(1 + z) (docs/ln.md, section 4), z = z_hi + z_lo exact
# and double-word (|z_lo| <= 2^-53 |z_hi|): the computed P against ln(1 + z), as
# a relative error. Written by generators/ln_certificates.py.
#
#   P = add_f64(add(z, (-z_hi^2/2 as a double-word)), RN(t - RN(z_hi z_lo)))
#
# Each binary64 rounding is modelled by its relative error, at most 2^-53: no
# intermediate underflows ({Z_MIN} <= |z_hi| keeps every magnitude above
# 2^-200, or exactly zero). From their own certificates:
#   t = T (1 + et), |et| <= {TAIL}                 (formal/ln/tail.g)
#   ln(1 + z) - z + z^2/2 = Tz + a, |a| <= rho |Tz|, rho = {d['poly_bound']}
#     (generators/ln_poly.sollya, supnorm, relative; Tz = z^3 W(z))
#   the double-word additions' relative bounds, machine-checked in binary64
#   (docs/double-word.md): add 3u^2/(1 - 4u) (d1), add_f64 2u^2 (d2).
# -z_hi^2 / 2 is exact: z_hi^2 = sh + sl by two_prod, and halving is exact.

{coefficients(d)}

zl = zh * dl;
z = zh + zl;
W = {horner('zh')};
Wz = {horner('z')};
T = zh * zh * zh * W;
Tz = z * z * z * Wz;
D = {' + '.join(terms)};

t = T * (1 + et);
c = zh * zl * (1 + ec);
u = (t - c) * (1 + eu);
B = -(zh * zh) / 2;
P1 = (z + B) * (1 + d1);
P = (P1 + u) * (1 + d2);
a = al * Tz;
L = z - z * z / 2 + Tz + a;

{{ |zh| in [{Z_MIN}, 0.0078126] /\\ {sym('dl', '1b-53')} /\\ {sym('et', TAIL)}
  /\\ {sym('ec', '1b-53')} /\\ {sym('eu', '1b-53')} /\\ {sym('al', rho)}
  /\\ {sym('d1', dw_add)} /\\ {sym('d2', '1b-105')}
  -> (P - L) / L in [-{POLY}, {POLY}] }}

# P - L = zl^2/2 + (T - Tz) + T et - zh zl ec + (t - c) eu - a + (z + B) d1
#         + ((z + B)(1 + d1) + u) d2; each term divided by zh, then by L / zh.
(P - L) / L -> ((P - L) / zh) / (L / zh);
L / zh -> (1 + dl) - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh);
(P - L) / zh -> zh * dl * dl / 2 + (T - Tz) / zh + (zh * zh * W) * et - zh * dl * ec
               + ((t - c) / zh) * eu - al * (Tz / zh) + ((z + B) / zh) * d1
               + (((z + B) * (1 + d1) + u) / zh) * d2;
# z^3 W(z) - zh^3 W(zh) = (z^3 - zh^3) W(z) + zh^3 (W(z) - W(zh)), and
# z^k - zh^k = zl (z^(k-1) + ... + zh^(k-1)).
(T - Tz) / zh -> -dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D);
Tz / zh -> (1 + dl) * z * z * Wz;
(t - c) / zh -> zh * zh * W * (1 + et) - zh * dl * (1 + ec);
(z + B) / zh -> 1 + dl - zh / 2;
u / zh -> ((t - c) / zh) * (1 + eu);
((z + B) * (1 + d1) + u) / zh -> ((z + B) / zh) * (1 + d1) + u / zh;
'''


def least_ln_1p():
    """The least |ln(1 + x)| on ln_1p's general branch, |x| >= 2^-7 (section 7)."""
    with mpmath.workprec(200):
        return frac(mpmath.log(1 + mpmath.mpf(2) ** -7))


def fast_ln_1p():
    """ln_1p's fast path (section 7): Y_h from ln's fast path at h, plus d = RN(l/h)."""
    v = least_ln_1p()
    t = Fraction(1, 2**53) * (1 + Fraction(1, 2**52))  # |l/h| <= u (1 + 2u)
    # delta = ln(1 + l/h): |delta| <= t / (1 - t), and |l/h - delta| <= t^2 / (2 (1 - t)).
    kd = up(t / (1 - t) / v)
    rr = up(t * t / (2 * (1 - t)) / v)
    return f'''# ln_1p's fast path on its general branch (docs/ln.md, section 7), |x| >= 2^-7:
# (h, l) = two_sum(1, x), so ln(1 + x) = ln h + delta, delta = ln(1 + l/h).
#   Yh = ln h (1 + eh): ln's fast path at h (formal/ln/fast_b.g, fast_c.g);
#   d = RN(l / h) = (l / h)(1 + eq); Y = add_f64(Yh, d), relative error e3.
# Over v = ln(1 + x), |v| >= ln(1 + 2^-7): kd = delta / v and kw = ln h / v =
# 1 - kd; rr = (l/h - delta) / v. Written by generators/ln_certificates.py.

kw = 1 - kd;
Y = (kw * (1 + eh) + (kd + rr) * (1 + eq)) * (1 + e3);

{{ {sym('kd', kd)} /\\ {sym('rr', rr)} /\\ {sym('eh', FAST)}
  /\\ {sym('eq', '1b-53')} /\\ {sym('e3', '1b-105')}
  -> Y - 1 in [-{FAST_LN_1P}, {FAST_LN_1P}] }}

Y - 1 -> (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3;
'''


def accurate_ln_1p_dz():
    """ln_1p's accurate path (section 7): z' = (y R - 1) + R l 2^-E in Q128, one
    addition within 2^-126 max(|a|, |b|) <= 2^-126 2^-7; ln(1 + .) is
    1/(1 - 0.0078127)-Lipschitz there. Relative to |ln(1 + x)|."""
    dz = Fraction(1, 2**133)
    return dz / (1 - Fraction(78127, 10_000_000)) / least_ln_1p()


def fast(d, case):
    dw_add = up(Fraction(3, 2**106) / (1 - Fraction(4, 2**53)))
    dt, lam = up(d['worst_dw']), up(d['lam'])
    dp = POLY
    if case == 'a':
        return f'''# The fast path's ln x (docs/ln.md, section 4), case A: E = 0 and R[i] = 1,
# so ln x = ln(1 + z), and the result is P through two exact additions of zero;
# their bounds are kept so the pipeline is one. Relative to ln x:
#   Y = (1 + dP) (1 + e1) (1 + e2), dP from formal/ln/p.g.
# Written by generators/ln_certificates.py.

Y = (1 + dP) * (1 + e1) * (1 + e2);

{{ {sym('dP', dp)} /\\ {sym('e1', dw_add)} /\\ {sym('e2', dw_add)}
  -> Y - 1 in [-{FAST}, {FAST}] }}
'''
    title, k = {
        'b': ('case B: E = 0 and R[i] != 1', d['case_b']),
        'c': ('case C: E != 0', d['case_c']),
    }[case]
    k1 = 'k1 = 1 - k2 - k3;' if case == 'c' else 'k1 = 0;'
    k_hyp = f"{sym('k3', up(k['k3']))}" + (f" /\\ {sym('k2', up(k['k2']))}" if case == 'c' else '')
    k2_def = '' if case == 'c' else 'k2 = 1 - k3;\n'
    return f'''# The fast path's ln x (docs/ln.md, section 4), {title}.
# Written by generators/ln_certificates.py.
#
# ln x = E ln 2 + (-ln R[i]) + ln(1 + z). With k1, k2, k3 those three terms over
# ln x (k1 + k2 + k3 = 1; their bounds from generators/ln_constants.py, least
# |ln x| = {float(k['lnx']):.6f}), the result over ln x is
#   Y = (k1 (1 + lam) + (k2 (1 + dT) + k3 (1 + dP)) (1 + e1)) (1 + e2)
#   dT: -ln R[i]'s double-word error (generated), lam: E ln 2's (generated);
#   dP: formal/ln/p.g; e1, e2: the double-word additions, 3u^2/(1 - 4u) each.

{k2_def}{k1}
Y = (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * (1 + e2);

{{ {k_hyp} /\\ {sym('dT', dt)} /\\ {sym('lam', lam)}
  /\\ {sym('dP', dp)} /\\ {sym('e1', dw_add)} /\\ {sym('e2', dw_add)}
  -> Y - 1 in [-{FAST}, {FAST}] }}

Y - 1 -> k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1
         + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2;
'''


def level(k, prev, x_lo, x_hi, bound):
    return f'''# Level {k} of ln(1 + z)'s series in Q128 (docs/ln.md, section 6):
# G_{k} = (1/{k}) - z G_{k + 1} against X_{k} = 1/{k} - z X_{k + 1}, given
# |G_{k + 1} - X_{k + 1}| <= {prev}. Written by generators/ln_certificates.py.

Gn = Xn + En;
G = (1 / {k}) * (1 + kk) - (z * Gn) * (1 + m) + s;
X = 1 / {k} - z * Xn;

{{ z in [-0.0078126, 0.0078126] /\\ Xn in [{x_lo}, {x_hi}]
  /\\ {sym('En', prev)}
  /\\ kk in [-1b-127, 1b-127] /\\ m in [-1b-127, 0] /\\ s in [-1b-126, 1b-126]
  -> G - X in [-{bound}, {bound}] }}

G - X -> (1 / {k}) * kk - z * (En + Gn * m) + s;
'''


def accurate(d):
    files = {}
    # G_DEGREE = 1/DEGREE as a constant, relative error below 2^-127.
    e_prev = Fraction(1, DEGREE) * U
    prev = up(e_prev)
    e_prev = value(prev)
    for k in range(DEGREE - 1, 0, -1):
        # X_(k+1) = sum_j (-z)^j / (k + 1 + j), alternating and decreasing:
        # within [1/(k+1) - |z|/(k+2), 1/(k+1) + |z|/(k+2)].
        x_lo = Fraction(1, k + 1) - Z / (k + 2)
        x_hi = Fraction(1, k + 1) + Z / (k + 2)
        g_max = x_hi + e_prev
        # |kk|/k + |z| (E_(k+1) + |G_(k+1)| 2^-127) + 2^-126 (operands below 1).
        bound = up(Fraction(1, k) * U + Z * (e_prev + g_max * U) + 2 * U)
        files[f'accurate_level_{k:02}.g'] = level(
            k, prev, f'{float(x_lo * Fraction(99, 100)):.9f}', f'{float(x_hi * Fraction(101, 100)):.9f}', bound)
        prev, e_prev = bound, value(bound)
    # G_1 approximates ln(1 + z)/z: the levels' error plus the truncation after
    # z^(DEGREE-1), at most the first omitted term, |z|^DEGREE / (DEGREE + 1)
    # (alternating, decreasing).
    e1 = up(e_prev + Z ** DEGREE / (DEGREE + 1))
    with mpmath.workprec(200):
        zm = mpmath.mpf(Z.numerator) / Z.denominator
        x1_lo, x1_hi = mpmath.log(1 + zm) / zm, mpmath.log(1 - zm) / -zm
    x1 = f'[{float(x1_lo) * 0.999:.6f}, {float(x1_hi) * 1.001:.6f}]'
    head = f'''# The accurate path's result over ln x (docs/ln.md, section 6), {{title}}.
# Written by generators/ln_certificates.py. In Q128: G = z G_1 with
# |G_1 - ln(1 + z)/z| <= E1 (the levels and the truncation), X1 = ln(1 + z)/z;
# mz, mL: products' truncations; eN, eL: -ln R[i]'s and ln 2's constants;
# s1, s2: the additions, 2^-126 max(|a|, |b|), over |ln x|; dz: ln_1p's
# rounding of z' (section 7), 0 for ln.
'''
    common = f"{sym('E1', e1)} /\\ X1 in {x1} /\\ mz in [-1b-127, 0]"
    files['accurate_sum_a.g'] = head.format(title='case A: E = 0 and R[i] = 1, so ln x = z X1') + f'''
Y = (X1 + E1) * (1 + mz) / X1;

{{ {common}
  -> Y - 1 in [-{ACCURATE}, {ACCURATE}] }}

Y - 1 -> E1 / X1 + (1 + E1 / X1) * mz;
'''
    dzr = up(accurate_ln_1p_dz())
    kb = d['case_b']
    s2b = up(2 * U * max(kb['k2'], kb['k3']))
    files['accurate_sum_b.g'] = head.format(title='case B: E = 0 and R[i] != 1') + f'''#   ln x = N + z X1, with k2 = N / ln x and k3 = z X1 / ln x (generated).

k2 = 1 - k3;
q = E1 / X1;
Y = k2 * (1 + eN) + k3 * (1 + q) * (1 + mz) + dz + s2;

{{ {sym('k3', up(kb['k3']))} /\\ {common}
  /\\ {sym('eN', '1b-127')} /\\ {sym('s2', s2b)} /\\ {sym('dz', dzr)}
  -> Y - 1 in [-{ACCURATE}, {ACCURATE}] }}

Y - 1 -> k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2;
'''
    kc = d['case_c']
    s1c = up(2 * U * max(kc['k1'], kc['k2']))
    s2c = up(2 * U * (1 + kc['k3']))
    files['accurate_sum_c.g'] = head.format(title='case C: E != 0') + f'''#   ln x = E ln 2 + N + z X1, with k1, k2, k3 those terms over ln x (generated).

k1 = 1 - k2 - k3;
q = E1 / X1;
Y = k1 * (1 + eL) * (1 + mL) + k2 * (1 + eN) + s1 + k3 * (1 + q) * (1 + mz) + dz + s2;

{{ {sym('k2', up(kc['k2']))} /\\ {sym('k3', up(kc['k3']))} /\\ {common}
  /\\ {sym('eN', '1b-127')} /\\ {sym('eL', '1b-127')} /\\ mL in [-1b-127, 0]
  /\\ {sym('s1', s1c)} /\\ {sym('s2', s2c)} /\\ {sym('dz', dzr)}
  -> Y - 1 in [-{ACCURATE}, {ACCURATE}] }}

Y - 1 -> k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2;
'''
    return files


def generate():
    d = ln_constants.derive()
    files = {'tail.g': tail(d), 'p.g': poly(d)}
    for case in 'abc':
        files[f'fast_{case}.g'] = fast(d, case)
    files['fast_ln_1p.g'] = fast_ln_1p()
    files.update(accurate(d))
    return files


def main():
    files = generate()
    check = '--check' in sys.argv[1:]
    if check:
        present = {p.name for p in DIR.glob('*.g')}
        if present != set(files):
            sys.exit(f'formal/ln holds {sorted(present ^ set(files))} unexpectedly')
    for name, text in files.items():
        path = DIR / name
        if check:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.write_text(text)


if __name__ == '__main__':
    main()
