#!/usr/bin/env python3
"""Writes the Gappa certificates of asin's fast path (docs/asin.md) into
formal/asin.

No number in a certificate is typed by hand: coefficients are the generated
tables' (generators/asin_constants.py), the polynomial errors are Sollya's
(generators/asin_poly.out), the double-word errors are the table generator's,
and every other hypothesis is a bound certified elsewhere (named where it is
used) or derived here in exact rational arithmetic, widened by at least 1%
(`up`, `down`).

- eval_<kk>.g, kk = 01..45 (section 4): segment kk's evaluation, from the
  reduced argument t = th + tl to the binary64 tail, against the exact value
  of the segment's polynomial with the same coefficients.
- compose_<kk>.g: segment kk's fast result Y + V against asin(a + t), relative.
- series.g: the series below 1/128 against asin z, relative.
- sqrt.g and complement.g: the complement's z = sqrt((1 - x)/2) as a
  double-word, and pi/2 - 2 asin(z) against asin x, relative.

With --check, fails if the committed certificates differ from a fresh
generation. Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

import mpmath

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import asin_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/asin'
T_LIT = '0.0078126'
T = Fraction(78126, 10_000_000)
U = Fraction(1, 2**53)
TL = Fraction(87, 10**20) / 10  # |tl| <= 2^-53 T < 8.7e-19 (tl is t_lo, normalized)
DW_ADD = '776b-114'      # add and sub: 3u^2/(1 - 4u), widened (docs/double-word.md)
DW_ADD_F = Fraction(776, 2**114)
DW_ACC = Fraction(1, 2**107)  # the tables' double-words, relative (asin_constants.py)
FAST = Fraction(1, 2**62)     # eps1 of the rounding test (docs/asin.md section 6)


def frac(v):
    if isinstance(v, Fraction):
        return v
    man, exp = mpmath.mpf(v).man_exp
    return Fraction(int(man)) * Fraction(2) ** int(exp)


def lit(v):
    """An exact Gappa literal for a Fraction with a power-of-two denominator."""
    v = frac(v)
    assert v.denominator & (v.denominator - 1) == 0
    n = v.denominator.bit_length() - 1
    return f'{v.numerator}b-{n}' if n else f'{v.numerator}'


def up(v):
    v = abs(frac(v)) * Fraction(101, 100)
    e = -math.floor(math.log2(v)) + 9
    return f'{math.ceil(v * 2**e)}b-{e}'


def down(v):
    v = abs(frac(v)) * Fraction(99, 100)
    e = -math.floor(math.log2(v)) + 9
    return f'{math.floor(v * 2**e)}b-{e}'


def hexf(x):
    return float(x).hex()


def hex_fraction(text):
    mantissa, exponent = text.lstrip('-')[2:].split('p')
    whole, _, fraction = mantissa.partition('.')
    return Fraction(int(whole + fraction, 16)) * Fraction(2) ** (int(exponent) - 4 * len(fraction))


def asin_bounds(k):
    """Rigorous lower and upper bounds of asin on [a - T, a + T], a = k/64,
    from mpmath interval arithmetic (asin v = atan2(v, sqrt(1 - v^2)))."""
    iv = mpmath.iv
    iv.prec = 200
    a = iv.mpf(k) / 64
    lo = a - iv.mpf(78126) / 10**7
    hi = a + iv.mpf(78126) / 10**7
    f = lambda v: iv.atan2(v, iv.sqrt(1 - v * v))  # noqa: E731
    return frac(mpmath.mpf(f(lo).a)), frac(mpmath.mpf(f(hi).b))


def eval_certificate(k, row, bound):
    """Segment k's tail evaluation against the exact polynomial (section 4).
    row = [y_hi, y_lo, c_hi, c_lo, g0..g8]."""
    c_hi, c_lo, g = row[2], row[3], row[4:]
    dg_poly = sum(Fraction(j) * abs(frac(g[j])) * T ** (j - 1) for j in range(1, 9))
    dg = TL * dg_poly  # |G(th + tl) - G(th)| <= |tl| sup|G'|, |tl| <= 2^-53 T
    lines = [
        f'# Segment {k:02d}\'s evaluation (docs/asin.md, section 4): with th, tl binary64',
        '# (the reduced argument t = th + tl, |tl| <= 2^-53 T), ph + pl = th c_hi exactly',
        '# (two_prod), and the rounded tail',
        '#   tail = s1 + n, s1 = pl + (th c_lo + tl c_hi), n = RN(th^2) g, g = Horner(th),',
        '# against the exact value of (c_hi + c_lo) t + t^2 G(t) after ph. dg bounds',
        '# G(th + tl) - G(th) by the mean value theorem with sup|G\'| from the',
        '# coefficients, in exact rational arithmetic. Written by',
        '# generators/asin_certificates.py.',
        '',
        '@rnd = float<ieee_64, ne>;',
        '',
        f'c_hi = {hexf(c_hi)}; c_lo = {hexf(c_lo)};',
        *[f'g{j} = {hexf(g[j])};' for j in range(9)],
        '',
        'th = rnd(th_);',
        'tl = rnd(tl_);',
        'ph rnd= th * c_hi;',
        'pl = th * c_hi - ph;',
        'm1 rnd= th * c_lo;',
        'm2 rnd= tl * c_hi;',
        'm3 rnd= m1 + m2;',
        's1 rnd= pl + m3;',
        't2 rnd= th * th;',
        'hh8 = g8;',
    ]
    for i in range(7, -1, -1):
        lines.append(f'q{i} rnd= th * hh{i + 1};')
        lines.append(f'hh{i} rnd= g{i} + q{i};')
        lines.append(f'HH{i} = g{i} + th * {"g8" if i == 7 else f"HH{i + 1}"};')
    lines += [
        'n rnd= t2 * hh0;',
        'tail rnd= s1 + n;',
        'tt = th + tl;',
        'Vx = pl + c_lo * th + c_hi * tl + c_lo * tl + tt * tt * (HH0 + dg);',
        '',
        f'{{ th_ in [-{T_LIT}, {T_LIT}] /\\ tl_ in [-8.7e-19, 8.7e-19] /\\ dg in [-{up(dg)}, {up(dg)}]',
        f'  -> tail - Vx in [-{bound}, {bound}] }}',
        '',
    ]
    for i in range(7, -1, -1):
        prev, hprev = ('g8', 'g8') if i == 7 else (f'hh{i + 1}', f'HH{i + 1}')
        if i == 7:
            lines.append(f'hh7 - HH7 -> (hh7 - (g7 + q7)) + (q7 - th * g8);')
        else:
            lines.append(f'hh{i} - HH{i} -> (hh{i} - (g{i} + q{i})) + (q{i} - th * {prev}) + th * ({prev} - {hprev});')
    lines += [
        'tail - Vx -> (tail - (s1 + n)) + (s1 - (pl + m3)) + (m3 - (m1 + m2)) + (m1 - th * c_lo)',
        '  + (m2 - tl * c_hi) + (n - t2 * hh0) + hh0 * (t2 - th * th) + th * th * (hh0 - HH0)',
        '  - c_lo * tl + (th * th - tt * tt) * HH0 - tt * tt * dg;',
        'th * th - tt * tt -> -tl * (th + tt);',
    ]
    return '\n'.join(lines) + '\n', dg


def eval_bound(row):
    """The claimed bound of the tail evaluation: four times T^2 2^-52 sup|G|,
    which Gappa proves or refuses (the proven bounds are within 2^1.6 of it)."""
    g = row[4:]
    g_max = sum(abs(frac(c)) * T ** j for j, c in enumerate(g))
    return up(4 * T * T * U * 2 * g_max)


def compose_certificate(k, row, d, eval_bound_lit):
    """Segment k's fast result against asin(a + t), relative (section 4)."""
    a = Fraction(k, 64)
    a_min, a_max = asin_bounds(k)
    asin_a = frac(mpmath.asin(mpmath.mpf(k) / 64))
    c1 = frac(1 / mpmath.sqrt(1 - (mpmath.mpf(k) / 64) ** 2))
    values = d['values']
    e_poly = T * T * (hex_fraction(values[f'u{k:02d}0']) + hex_fraction(values[f'r{k:02d}0']))
    e_dy = DW_ACC * asin_a
    e_dc = DW_ACC * c1 * T
    e_eval = frac(Fraction(int(eval_bound_lit.split('b-')[0]), 2 ** int(eval_bound_lit.split('b-')[1])))
    total = (e_poly + e_dy + e_dc + e_eval) / a_min
    claim = (total * (1 + DW_ADD_F) + DW_ADD_F) * Fraction(101, 100)
    assert claim <= FAST * 3 / 4, f'segment {k}: {float(claim)} too large'
    bound = up(claim)
    lines = [
        f'# Segment {k:02d}\'s fast result (docs/asin.md, section 4): F = (Y + V)(1 + ea) against',
        '# A = asin(a + t), relative, with Y = asin(a) and V = c1 t + t^2 G(t) the tail.',
        '# The errors of X = Yv + Vv against A, each certified elsewhere or derived in',
        '# exact rational arithmetic by generators/asin_certificates.py:',
        '#   dY: the table\'s double-word of asin(a), relative error 2^-107',
        '#   dc: (c_hi + c_lo - c1) t, the double-word of c1 = 1/sqrt(1 - a^2)',
        '#   dP: t^2 (G - G_true), Sollya\'s supnorm plus the Taylor remainder (asin_poly.out)',
        f'#   dV: the tail\'s evaluation (formal/asin/eval_{k:02d}.g)',
        '#   ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md)',
        '',
        'X = A + dY + dc + dP + dV;',
        'F = X * (1 + ea);',
        '',
        f'{{ A in [{down(a_min)}, {up(a_max)}] /\\ dY in [-{up(e_dy)}, {up(e_dy)}] /\\ dc in [-{up(e_dc)}, {up(e_dc)}]',
        f'  /\\ dP in [-{up(e_poly)}, {up(e_poly)}] /\\ dV in [-{eval_bound_lit}, {eval_bound_lit}] /\\ ea in [-{DW_ADD}, {DW_ADD}]',
        f'  -> (F - A) / A in [-{bound}, {bound}] }}',
        '',
        '(F - A) / A -> ((dY + dc + dP + dV) * (1 + ea)) / A + ea { A <> 0 };',
    ]
    return '\n'.join(lines) + '\n', claim


def series_tail_certificate(values):
    """The series' tail zh^3 P(zh^2) in binary64 against the polynomial evaluated
    exactly (section 4), relative: written like trig's tails."""
    q = [values[f'p00{j}'] for j in range(4)]
    return f"""# The series' cubic term (docs/asin.md, section 4): with zh a binary64,
# 2^-28 <= zh <= {T_LIT},
#   u = RN(zh^2), p = q0 + u (q1 + u (q2 + u q3)), tail = RN(RN(zh u) p)
# against zh^3 P(zh^2), P the same polynomial evaluated exactly. All four
# coefficients are positive, so every operation is a relative one. Written by
# generators/asin_certificates.py.

@rnd = float<ieee_64, ne>;

{chr(10).join(f'q{j} = {q[j]};' for j in range(4))}

zh = rnd(zh_);
uh rnd= zh * zh;
p3 rnd= q2 + uh * q3;
p2 rnd= q1 + uh * p3;
ps rnd= q0 + uh * p2;
a3 rnd= zh * uh;
tail rnd= a3 * ps;
P3 = q2 + zh * zh * q3;
P2 = q1 + zh * zh * P3;
P = q0 + zh * zh * P2;
Tx = zh * zh * zh * P;

{{ zh_ in [1b-28, {T_LIT}] -> (tail - Tx) / Tx in [-1b-51, 1b-51] }}

(tail - Tx) / Tx -> (1 + (a3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1
  {{ Tx <> 0, zh <> 0, P <> 0, a3 <> 0, ps <> 0 }};
(a3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (uh - zh * zh) / (zh * zh)) * (1 + (a3 - zh * uh) / (zh * uh)) - 1
  {{ zh <> 0, uh <> 0 }};
"""


def series_compose_certificate(values):
    """The series' fast result against asin z (section 4), relative."""
    rc = Fraction(11, 10**6)  # (asin z - z)/z <= z^2/6 (1 + z^2) <= 1.02e-5 on z <= T
    # eps, the relative gap between the computed cubic term and asin z - z:
    # the tail's 2^-51 (series_tail.g), Sollya's 2^-54 (1 + 2^-23) for the polynomial
    # (asin_poly.out), and zl and the rounding of zh^2 inside z^3 P(z^2): 3.1 2^-53.
    eps = Fraction(1, 2**50)
    parts = Fraction(1, 2**51) + Fraction(1, 2**54) * (1 + Fraction(1, 2**23)) + Fraction(31, 10) * Fraction(1, 2**53)
    assert parts <= eps, 'the series eps pieces exceed 2^-50'
    claim = up(rc * eps * (1 + DW_ADD_F) + DW_ADD_F)
    return rf"""# The series' fast result (docs/asin.md, section 4): F = (z + c)(1 + ea) with
# z = zh + zl exactly, c = RN(RN(zh u) p), against A = asin z = z (1 + rc),
# relative. rc = (asin z - z)/z <= z^2/6 (1 + z^2) <= 1.1e-5 on z <= {T_LIT}; c
# differs from A - z by the relative eps, at most 2^-50: the tail's 2^-51
# (formal/asin/series_tail.g), Sollya's 2^-54 (1 + 2^-23) for the polynomial
# (asin_poly.out) and 3.1 2^-53 for zl and the rounding of zh^2 inside z^3 P(z^2);
# generators/asin_certificates.py asserts their sum is at most 2^-50.
# ea: add_f64, 2u^2 (docs/double-word.md). Written by
# generators/asin_certificates.py.

A = z * (1 + rc);
F = (z * (1 + rc * (1 + eps))) * (1 + ea);

{{ z in [1b-28, {T_LIT}] /\ rc in [0, 1.1e-5] /\ eps in [-1b-50, 1b-50] /\ ea in [-1b-104, 1b-104]
  -> (F - A) / A in [-{claim}, {claim}] }}

(F - A) / A -> (rc * eps + (1 + rc * (1 + eps)) * ea) / (1 + rc) {{ z <> 0, 1 + rc <> 0 }};
""", claim


def sqrt_certificate():
    """z = s + s_lo against the true root w of u (section 3)."""
    return rf"""# The complement's square root as a double-word (docs/asin.md, section 3): with w
# the real root of the exact u = (1 - x)/2, s = RN(w) (sqrt is correctly rounded),
# (ph, pl) = two_prod(s, s), s_lo = RN(RN(RN(u - ph) - pl)/(2 s)) and z = s + s_lo
# exactly (two_sum), z against w, relative. With e = s - w, u - s^2 = -e (s + w)
# and z - w = e^2/(2 s) plus the three roundings. Written by
# generators/asin_certificates.py.

@rnd = float<ieee_64, ne>;

w = w_;
u = w * w;
s = rnd(w);
s2 = 2 * s;
ph rnd= s * s;
pl = s * s - ph;
rr1 rnd= u - ph;
r2 rnd= rr1 - pl;
sl rnd= r2 / s2;
zv = s + sl;

{{ w_ in [1b-27, 0.3827] -> (zv - w) / w in [-1b-103, 1b-103] }}

(zv - w) / w -> ((s - w) * (s - w) / s2 + (rr1 - (u - ph)) / s2 + (r2 - (rr1 - pl)) / s2 + (sl - r2 / s2)) / w {{ w <> 0, s <> 0 }};
"""


def complement_certificate(z_claim, ez_lit):
    """pi/2 - 2 asin(z) against asin x (section 3), relative."""
    es = Fraction(11, 10) * Fraction(int(ez_lit.split('b-')[0]), 2 ** int(ez_lit.split('b-')[1]))
    total = z_claim + es + 2 * DW_ACC + DW_ADD_F
    claim = up(total * Fraction(101, 100) * (1 + DW_ADD_F) + DW_ADD_F)
    return rf"""# The complement's result (docs/asin.md, section 3): y = (H - D')(1 + ea) with
# H = pi/2 as a double-word (relative error eH <= 2^-107), D' = 2 F(z) exactly
# (F the fast result at the double-word z), against asin x = pi/2 - D, D = 2 asin w
# for w = sqrt((1 - x)/2). F = asin(zv)(1 + eF), eF the fast path's bound at its
# segment (formal/asin/compose_*.g, series_compose.g); zv = w (1 + ez) with ez
# from formal/asin/sqrt.g; asin(zv)/asin(w) - 1 = es, at most 1.1 ez since
# (w / asin w)/sqrt(1 - w^2) <= 1.055 on w <= 0.3827. ea: sub, 3u^2/(1 - 4u).
# Written by generators/asin_certificates.py.

Ax = H - D;
y = (H * (1 + eH) - D * (1 + es) * (1 + eF)) * (1 + ea);

{{ H in [1.570796326794896619, 1.570796326794896620] /\ D in [0, 0.7854] /\ Ax in [0.78539816339744, 1.5707963267948967]
  /\ eH in [-{lit(DW_ACC)}, {lit(DW_ACC)}] /\ es in [-{up(es)}, {up(es)}] /\ eF in [-{up(z_claim)}, {up(z_claim)}]
  /\ ea in [-{DW_ADD}, {DW_ADD}]
  -> (y - Ax) / Ax in [-{claim}, {claim}] }}

(y - Ax) / Ax -> ((H * eH - D * ((1 + es) * (1 + eF) - 1)) * (1 + ea)) / Ax + ea {{ Ax <> 0 }};
""", Fraction(int(claim.split('b-')[0]), 2 ** int(claim.split('b-')[1]))


def trig_claim(name, pattern):
    """A bound certified in formal/trig, read from the certificate itself."""
    import re
    text = (ROOT / 'formal/trig' / name).read_text()
    m = re.search(pattern, text)
    assert m, f'{name}: no {pattern}'
    return m.group(1)


def identity_check():
    """The Newton certificates' rewrite hints are algebra Gappa takes on trust
    (the formal lane proves them in Coq): check them here in exact rational
    arithmetic at random points, so a slip fails generation."""
    import random
    rng = random.Random(0x6173696e)

    def r(lo, hi):
        return Fraction(rng.randrange(10**6, 10**9), 10**9) * (Fraction(hi) - Fraction(lo)) + Fraction(lo)

    def sym(b):
        return r(-b, b)

    for _ in range(200):
        # Direct: y1 - Y over Y.
        Y, eta = r('0.00001', '0.78'), sym(Fraction(1, 2**62))
        s0, c0, rr = r('0.1', '0.7'), r('0.7072', '1'), r('0.1', '0.5')
        sigma, gamma, ea, mx = sym(Fraction(1, 2**198)), sym(Fraction(1, 2**198)), sym(Fraction(1, 2**254)), r('0.1', '0.7')
        e, m, eb = sym(Fraction(650, 2**262)), -r(0, Fraction(1, 2**255)), sym(Fraction(1, 2**254))
        y0 = Y * (1 + eta)
        d = Y - y0
        x = s0 + c0 * d - rr * d * d
        rho = (x - s0 * (1 + sigma)) + ea * mx
        q = (rho * (1 + e) / (c0 * (1 + gamma))) * (1 + m)
        y1 = (y0 + q) + eb * y0
        kk = (1 + e) * (1 + m) / (1 + gamma) - 1
        t2, t3, t4 = -rr * Y * eta * eta / c0, -s0 * sigma / (c0 * Y), ea * mx / (c0 * Y)
        assert (y1 - Y) / Y == -eta * kk + (t2 + t3 + t4) * (1 + kk) + eb * (1 + eta), 'direct identity'
        # Complement: yf - Ax over Ax.
        Dt, fs = r('0.00001', '0.78'), r('0.89', '1')
        H, eH, ec = r('1.5707963', '1.5707964'), sym(Fraction(1, 2**257)), sym(Fraction(1, 2**254))
        d0 = Dt * (1 + eta)
        s0 = d0 * fs
        d = Dt - d0
        x = c0 - s0 * d - rr * d * d
        rho = (c0 * (1 + gamma) - x) + ea * mx
        q = (rho * (1 + e) / (s0 * (1 + sigma))) * (1 + m)
        d1 = (d0 + q) + eb * d0
        yf = (H * (1 + eH) - d1) + ec * H
        Ax = H - Dt
        kk = (1 + e) * (1 + m) / (1 + sigma) - 1
        u1, u2 = -eta * kk, rr * eta * eta / ((1 + eta) * fs)
        u3, u4 = c0 * gamma / (Dt * Dt * (1 + eta) * fs), ea * mx / (Dt * Dt * (1 + eta) * fs)
        u5 = eb * (1 + eta)
        assert (yf - Ax) / Ax == ((H * eH + ec * H) - Dt * (u1 + (u2 + u3 + u4) * (1 + kk) + u5)) / Ax, 'complement identity'
        # The series' composition and the square root's correction.
        z, rc, eps, ea2 = r('0.00001', '0.0078'), r('0', '0.00001'), sym(Fraction(1, 2**49)), sym(Fraction(1, 2**104))
        A, F = z * (1 + rc), (z * (1 + rc * (1 + eps))) * (1 + ea2)
        assert (F - A) / A == (rc * eps + (1 + rc * (1 + eps)) * ea2) / (1 + rc), 'series identity'
        w, s_, ph, rr1, r2_, sl = r('0.00001', '0.38'), r('0.00001', '0.38'), r('0', '0.1'), r('0', '0.1'), r('0', '0.1'), r('0', '0.1')
        u, pl, s2 = w * w, s_ * s_ - ph, 2 * s_
        zv = s_ + sl
        assert (zv - w) / w == ((s_ - w) * (s_ - w) / s2 + (rr1 - (u - ph)) / s2 + (r2_ - (rr1 - pl)) / s2 + (sl - r2_ / s2)) / w, 'sqrt identity'


def newton_certificates():
    """The accurate path's Newton step in Q256 (docs/asin.md, section 5)."""
    sin_claim = trig_claim('accurate_sin.g', r'Y - 1 in \[-(1b-\d+),')
    cos_claim = trig_claim('accurate_cos.g', r'Y - 1 in \[-(1b-\d+),')
    recip = trig_claim('recip_3.g', r'P - 1 in \[-(\d+b-\d+),')
    assert sin_claim == cos_claim == '1b-198', (sin_claim, cos_claim)
    identity_check()
    common = f"""# Hypotheses certified elsewhere or exact: eta, the start's relative error, is at
# most eps1 = 2^-62 (the fast path's bound, formal/asin/compose_*.g and
# complement.g, asserted by generators/asin_certificates.py; the start is
# y_hi + y_lo added in Q256, which errs by at most 2^-254 more); sigma and gamma,
# sin's and cos's relative errors at an exact argument, {sin_claim}
# (formal/trig/accurate_sin.g, accurate_cos.g, whose reduction term is zero here);
# e, Q256::recip's c y = 1 + e (formal/trig/recip_3.g); m, a Q256 product's
# truncation, [-2^-255, 0]; ea and eb, a Q256 sum's error, 2^-254 of its larger
# operand (docs/sin_cos.md, section 5). The Taylor remainder, the argument ranges
# and sin t/t >= 0.89 are proved in Coq in formal/asin/AsinFacts.v
# (taylor_sin, taylor_cos, quarter_pi_ranges, sin_ratio, sin_split_range,
# cos_split_range, y_lower, d_lower). Written by generators/asin_certificates.py.
"""
    direct = rf"""# The accurate path's Newton step for x <= SPLIT (docs/asin.md, section 5):
#   y1 = y0 + (x - sin y0)/cos y0
# in Q256 from y0 = Y (1 + eta), Y = asin x in [2^-26, pi/4), against Y, relative.
#   x = sin Y = s0 + c0 d + R, d = Y - y0, R = -rr d^2   (Taylor, rr in [-2^-60, 0.5000001], formal/asin/AsinFacts.v)
#   S = s0 (1 + sigma); rho = (x - S) + ea mx; ri = (1 + e)/(c0 (1 + gamma))
#   q = (rho ri)(1 + m); y1 = (y0 + q) + eb y0
# so (y1 - Y)/Y = -eta kk + (t2 + t3 + t4)(1 + kk) + eb (1 + eta) with
# kk = (1 + e)(1 + m)/(1 + gamma) - 1 and t2 = R/(c0 Y), t3 = -s0 sigma/(c0 Y),
# t4 = ea mx/(c0 Y): the quadratic term t2 dominates.
{common}
y0 = Y * (1 + eta);
d = Y - y0;
R = -rr * d * d;
x = s0 + c0 * d + R;
S = s0 * (1 + sigma);
rho = (x - S) + ea * mx;
ri = (1 + e) / (c0 * (1 + gamma));
q = (rho * ri) * (1 + m);
y1 = (y0 + q) + eb * y0;
kk = (1 + e) * (1 + m) / (1 + gamma) - 1;
t2 = -rr * Y * eta * eta / c0;
t3 = -s0 * sigma / (c0 * Y);
t4 = ea * mx / (c0 * Y);

{{ Y in [1b-26, 0.7854] /\ eta in [-1b-62, 1b-62] /\ s0 in [0, 0.7072] /\ c0 in [0.7071, 1]
  /\ rr in [-1b-60, 0.5000001] /\ sigma in [-{sin_claim}, {sin_claim}] /\ gamma in [-{cos_claim}, {cos_claim}]
  /\ ea in [-1b-254, 1b-254] /\ mx in [0, 0.7072] /\ e in [-{recip}, {recip}] /\ m in [-1b-255, 0]
  /\ eb in [-1b-254, 1b-254]
  -> (y1 - Y) / Y in [-1b-124, 1b-124] }}

(y1 - Y) / Y -> -eta * kk + (t2 + t3 + t4) * (1 + kk) + eb * (1 + eta) {{ Y <> 0, c0 <> 0, 1 + gamma <> 0 }};
"""
    complement = rf"""# The accurate path's Newton step for x > SPLIT (docs/asin.md, section 5):
#   d1 = d0 + (cos d0 - x)/sin d0, result pi/2 - d1
# in Q256 from d0 = D (1 + eta), D = acos x in [2^-27, pi/4), against Ax = pi/2 - D,
# relative. The start is the fast path's delta, accurate relative to D.
#   x = cos D = c0 - s0 d - R', d = D - d0, R' = rr d^2   (Taylor, rr in [-2^-60, 0.5000001], formal/asin/AsinFacts.v)
#   s0 = sin d0 = d0 fs, fs in [0.89, 1] (sin t/t >= 0.9 for t <= pi/4)
#   C = c0 (1 + gamma); rho = (C - x) + ea mx; ri = (1 + e)/(s0 (1 + sigma))
#   q = (rho ri)(1 + m); d1 = (d0 + q) + eb d0; yf = (H (1 + eH) - d1) + ec H
# so d1 - D = D (u1 + (u2 + u3 + u4)(1 + kk) + u5) with kk = (1 + e)(1 + m)/(1 + sigma) - 1,
# u1 = -eta kk, u2 = rr eta^2/((1 + eta) fs), u3 = c0 gamma/(D^2 (1 + eta) fs),
# u4 = ea mx/(D^2 (1 + eta) fs), u5 = eb (1 + eta). H is pi/2 in Q256 (relative
# error 2^-257.3); ec is the final sum's error.
{common}
d0 = Dt * (1 + eta);
s0 = d0 * fs;
d = Dt - d0;
x = c0 - s0 * d - rr * d * d;
rho = (c0 * (1 + gamma) - x) + ea * mx;
ri = (1 + e) / (s0 * (1 + sigma));
q = (rho * ri) * (1 + m);
d1 = (d0 + q) + eb * d0;
yf = (H * (1 + eH) - d1) + ec * H;
Ax = H - Dt;
kk = (1 + e) * (1 + m) / (1 + sigma) - 1;
u1 = -eta * kk;
u2 = rr * eta * eta / ((1 + eta) * fs);
u3 = c0 * gamma / (Dt * Dt * (1 + eta) * fs);
u4 = ea * mx / (Dt * Dt * (1 + eta) * fs);
u5 = eb * (1 + eta);

{{ Dt in [1b-27, 0.7854] /\ eta in [-1b-62, 1b-62] /\ fs in [0.89, 1] /\ c0 in [0.7071, 1]
  /\ rr in [-1b-60, 0.5000001] /\ sigma in [-{sin_claim}, {sin_claim}] /\ gamma in [-{cos_claim}, {cos_claim}]
  /\ ea in [-1b-254, 1b-254] /\ mx in [0, 1.0001] /\ e in [-{recip}, {recip}] /\ m in [-1b-255, 0]
  /\ eb in [-1b-254, 1b-254] /\ ec in [-1b-254, 1b-254] /\ eH in [-1b-257, 1b-257]
  /\ H in [1.570796326794896619, 1.570796326794896620]
  -> (yf - Ax) / Ax in [-1b-124, 1b-124] }}

(yf - Ax) / Ax -> ((H * eH + ec * H) - Dt * (u1 + (u2 + u3 + u4) * (1 + kk) + u5)) / Ax {{ Ax <> 0, Dt <> 0, fs <> 0, 1 + eta <> 0, 1 + sigma <> 0 }};
"""
    return {'newton_direct.g': direct, 'newton_complement.g': complement}


def derive():
    return asin_constants.derive()


def generate():
    d = derive()
    out = {}
    worst = Fraction(0)
    claims = {}
    for k in range(1, asin_constants.SEGMENTS + 1):
        row = d['rows'][k - 1]
        bound = eval_bound(row)
        text, _ = eval_certificate(k, row, bound)
        out[f'eval_{k:02d}.g'] = text
        text, claim = compose_certificate(k, row, d, bound)
        out[f'compose_{k:02d}.g'] = text
        claims[k] = claim
        worst = max(worst, claim)
    values = d['values']
    out['series_tail.g'] = series_tail_certificate(values)
    text, series_claim = series_compose_certificate(values)
    out['series_compose.g'] = text
    out['sqrt.g'] = sqrt_certificate()
    # The complement reaches segments k <= 24 (z <= 0.3827) and the series.
    z_claim = max(
        [Fraction(int(series_claim.split('b-')[0]), 2 ** int(series_claim.split('b-')[1]))]
        + [claims[k] for k in range(1, 25)])
    text, y_claim = complement_certificate(z_claim, '1b-103')
    out['complement.g'] = text
    out.update(newton_certificates())
    worst = max(worst, y_claim)
    assert worst <= FAST, f'fast path bound 2^{math.log2(worst):.2f} exceeds 2^-62'
    return out, worst


def main():
    files, worst = generate()
    DIR.mkdir(parents=True, exist_ok=True)
    if '--check' in sys.argv[1:]:
        for name, text in files.items():
            if (DIR / name).read_text() != text:
                sys.exit(f'{DIR / name} differs from a fresh generation')
        return
    for name, text in files.items():
        (DIR / name).write_text(text)
    print(f'{len(files)} certificates; worst segment bound 2^{math.log2(worst):.2f}')


if __name__ == '__main__':
    main()
