#!/usr/bin/env python3
"""Writes the Gappa certificates of atan2's fast and accurate paths
(docs/atan2.md) into formal/atan2.

No number in a certificate is typed by hand: coefficients are the generated
tables' (generators/atan2_constants.py), the polynomial errors are Sollya's
(generators/atan2_poly.out), and every other hypothesis is a bound certified
elsewhere (named where it is used) or derived here in exact rational
arithmetic, widened by at least 1% (`up`).

- eval_<kk>.g, kk = 01..64 (section 4): segment kk's evaluation, from the
  reduced argument s = sh + sl to the binary64 tail, against the exact value of
  the segment's polynomial with the same coefficients (the same model as
  asin's; written by asin_certificates.eval_certificate).
- compose_<kk>.g: segment kk's fast result Y + V against atan(a + s), relative.
- series_tail.g and series_compose.g: the series below 1/128 against atan t.
- divide.g: the double-word ratio t = qh + ql against n/d (section 3).
- half_minus.g, half_plus.g and pi_minus.g: the three forms that add a
  constant to phi (section 3).
- newton.g: the accurate path's cubic step (section 5).

With --check, fails if the committed certificates differ from a fresh
generation. Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

import mpmath

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import asin_certificates as ac  # noqa: E402
import atan2_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/atan2'
T_LIT = ac.T_LIT
T = ac.T
up, lit, frac, hex_fraction = ac.up, ac.lit, ac.frac, ac.hex_fraction
DW_ADD, DW_ADD_F, DW_ACC = ac.DW_ADD, ac.DW_ADD_F, ac.DW_ACC
FAST = Fraction(1, 2**62)  # eps1 of the rounding test (docs/atan2.md section 6)
# The quotient's double-word: relative error at most 2^-53 (2 * 2^-53 + 2^-106).
EPS_T = Fraction(1, 2**104)
# The tail evaluation's claimed bound: BOUND_FACTOR T^2 2^-53 sup|G|; Gappa proves 5.4 to 5.95 of it (asin uses 8).
BOUND_FACTOR = Fraction(13, 2)


def eval_bound(row):
    g_max = sum(abs(frac(c)) * T ** j for j, c in enumerate(row[4:]))
    return up(BOUND_FACTOR * T * T * ac.U * g_max)


def value(literal):
    n, e = literal.split('b-')
    return Fraction(int(n), 2 ** int(e))


def sym(name, literal):
    return f'{name} in [-{literal}, {literal}]'


def atan_bounds(k):
    """Rigorous lower and upper bounds of atan on [a - T, a + T], a = k/64."""
    iv = mpmath.iv
    iv.prec = 200
    a = iv.mpf(k) / 64
    lo = a - iv.mpf(78126) / 10**7
    hi = a + iv.mpf(78126) / 10**7
    return frac(mpmath.mpf(iv.atan2(lo, iv.mpf(1)).a)), frac(mpmath.mpf(iv.atan2(hi, iv.mpf(1)).b))


def compose_certificate(k, row, d, eval_bound_lit):
    """Segment k's fast result against atan(a + s), relative (section 4)."""
    a_min, a_max = atan_bounds(k)
    atan_a = frac(mpmath.atan(mpmath.mpf(k) / 64))
    c1 = frac(1 / (1 + (mpmath.mpf(k) / 64) ** 2))
    values = d['values']
    e_poly = T * T * (hex_fraction(values[f'u{k:02d}0']) + hex_fraction(values[f'r{k:02d}0']))
    e_dy = DW_ACC * atan_a
    e_dc = DW_ACC * c1 * T
    e_eval = value(eval_bound_lit)
    total = (e_poly + e_dy + e_dc + e_eval) / a_min
    claim = (total * (1 + DW_ADD_F) + DW_ADD_F) * Fraction(101, 100)
    assert claim <= FAST * 3 / 4, f'segment {k}: {float(claim)} too large'
    bound = up(claim)
    lines = [
        f"# Segment {k:02d}'s fast result (docs/atan2.md, section 4): F = (Y + V)(1 + ea) against",
        '# A = atan(a + s), relative, with Y = atan(a) and V = c1 s + s^2 G(s) the tail.',
        '# The errors of X = Yv + Vv against A, each certified elsewhere or derived in',
        '# exact rational arithmetic by generators/atan2_certificates.py:',
        "#   dY: the table's double-word of atan(a), relative error 2^-107",
        '#   dc: (c_hi + c_lo - c1) s, the double-word of c1 = 1/(1 + a^2)',
        "#   dP: s^2 (G - G_true), Sollya's supnorm plus the Taylor remainder (atan2_poly.out)",
        f"#   dV: the tail's evaluation (formal/atan2/eval_{k:02d}.g)",
        '#   ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md)',
        '',
        'X = A + dY + dc + dP + dV;',
        'F = X * (1 + ea);',
        '',
        f'{{ A in [{ac.down(a_min)}, {up(a_max)}] /\\ dY in [-{up(e_dy)}, {up(e_dy)}] /\\ dc in [-{up(e_dc)}, {up(e_dc)}]',
        f'  /\\ dP in [-{up(e_poly)}, {up(e_poly)}] /\\ dV in [-{eval_bound_lit}, {eval_bound_lit}] /\\ ea in [-{DW_ADD}, {DW_ADD}]',
        f'  -> (F - A) / A in [-{bound}, {bound}] }}',
        '',
        '(F - A) / A -> ((dY + dc + dP + dV) * (1 + ea)) / A + ea { A <> 0 };',
    ]
    return '\n'.join(lines) + '\n', claim


def series_tail_certificate(values):
    """The series' tail zh^3 Q(zh^2) in binary64 against the polynomial
    evaluated exactly, relative. atan z = z - z^3 Q(z^2), Q = q0 - s (q1 - s (q2
    - s q3)) with every q_j positive; the kernel's P = -Q operation for operation,
    rounding being odd."""
    q = [values[f'p00{j}'].lstrip('-') for j in range(4)]
    return f"""# The series' cubic term (docs/atan2.md, section 4): with zh a binary64,
# 2^-100 <= zh <= {T_LIT},
#   u = RN(zh^2), p = q0 - u (q1 - u (q2 - u q3)), tail = RN(RN(zh u) p)
# against zh^3 Q(zh^2), Q the same polynomial evaluated exactly. The kernel
# evaluates P = -Q with the signs of the coefficients, which is the same
# operations negated (rounding to nearest is odd). Each subtraction's second
# term is at most 2^-13 of the first, so every operation is a relative one. For
# zh below 2^-100 the cubic term is below 2^-200 zh, negligible against every
# bound it enters. Written by generators/atan2_certificates.py.

@rnd = float<ieee_64, ne>;

{chr(10).join(f'q{j} = {q[j]};' for j in range(4))}

zh = rnd(zh_);
uh rnd= zh * zh;
p3 rnd= q2 - uh * q3;
p2 rnd= q1 - uh * p3;
ps rnd= q0 - uh * p2;
a3 rnd= zh * uh;
tail rnd= a3 * ps;
P3 = q2 - zh * zh * q3;
P2 = q1 - zh * zh * P3;
P = q0 - zh * zh * P2;
Tx = zh * zh * zh * P;

{{ zh_ in [1b-100, {T_LIT}] -> (tail - Tx) / Tx in [-1b-51, 1b-51] }}

(tail - Tx) / Tx -> (1 + (a3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1
  {{ Tx <> 0, zh <> 0, P <> 0, a3 <> 0, ps <> 0 }};
(a3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (uh - zh * zh) / (zh * zh)) * (1 + (a3 - zh * uh) / (zh * uh)) - 1
  {{ zh <> 0, uh <> 0 }};
"""


def series_compose_certificate(values):
    """The series' fast result against atan z, relative."""
    rc = Fraction(21, 10**6)  # (z - atan z)/z <= z^2/3 <= 2.04e-5 on z <= T
    eps = Fraction(1, 2**50)
    parts = Fraction(1, 2**51) + Fraction(1, 2**54) * (1 + Fraction(1, 2**23)) + Fraction(31, 10) * Fraction(1, 2**53)
    assert parts <= eps, 'the series eps pieces exceed 2^-50'
    claim = up(rc * eps * (1 + DW_ADD_F) + DW_ADD_F)
    return rf"""# The series' fast result (docs/atan2.md, section 4): F = (z - c)(1 + ea) with
# z = zh + zl exactly, c = RN(RN(zh u) |p|) (the cubic term, positive), against
# A = atan z = z (1 - rc), relative. rc = (z - atan z)/z <= z^2/3 <= 2.1e-5 on
# z <= {T_LIT}; c differs from z - A by the relative eps, at most 2^-50: the
# tail's 2^-51 (formal/atan2/series_tail.g), Sollya's 2^-54 (1 + 2^-23) for the
# polynomial (atan2_poly.out) and 3.1 2^-53 for zl and the rounding of z^2 inside
# z^3 Q(z^2); generators/atan2_certificates.py asserts their sum is at most 2^-50.
# ea: add_f64, 2u^2 (docs/double-word.md). Written by
# generators/atan2_certificates.py.

A = z * (1 - rc);
F = (z * (1 - rc * (1 + eps))) * (1 + ea);

{{ z in [1b-100, {T_LIT}] /\ rc in [0, 2.1e-5] /\ eps in [-1b-50, 1b-50] /\ ea in [-1b-104, 1b-104]
  -> (F - A) / A in [-{claim}, {claim}] }}

(F - A) / A -> ea - (rc * eps * (1 + ea)) / (1 - rc) {{ z <> 0, 1 - rc <> 0 }};
""", claim


def divide_certificate():
    """t = qh + ql against n/d (section 3), relative."""
    return rf"""# The double-word ratio (docs/atan2.md, section 3): with n and d scaled so that
# d is in [1, 2) and n/d = tt in [2^-900, 1], q = RN(n/d) = tt (1 + e0), |e0| <= 2^-53.
# (p, pe) = two_prod(q, d) is exact and n - p is exact (Sterbenz), so the exact
# remainder is n - q d = -tt e0 d; its computed value is that times (1 + a) (the
# subtraction of pe) and ql = RN(r/d) = r (1 + b)/d. Then t = q + ql (fast_two_sum,
# exact) = tt + e0 tt - tt e0 (1 + a) (1 + b). Written by
# generators/atan2_certificates.py.

q = tt * (1 + e0);
ql = -(tt * e0) * (1 + a) * (1 + b);
t = q + ql;

{{ tt in [1b-900, 1] /\ e0 in [-1b-53, 1b-53] /\ a in [-1b-53, 1b-53] /\ b in [-1b-53, 1b-53]
  -> (t - tt) / tt in [-1b-104, 1b-104] }}

(t - tt) / tt -> -e0 * (a + b + a * b) {{ tt <> 0 }};
"""


def form_certificates(phi_claim):
    """The forms adding a constant to phi (section 3), relative to the angle."""
    es = up(phi_claim)
    certs = {}
    for name, c_lo, c_hi, sign, label in (
        ('half_minus', '0.7853981633974483', '1.5707963267948966', '-', 'pi/2 - phi'),
        ('half_plus', '1.5707963267948966', '2.356194490192345', '+', 'pi/2 + phi'),
        ('pi_minus', '2.356194490192344', '3.1415926535897936', '-', 'pi - phi'),
    ):
        const = {'half_minus': '1.5707963267948966', 'half_plus': '1.5707963267948966', 'pi_minus': '3.14159265358979323'}[name]
        const_hi = {'half_minus': '1.5707963267948967', 'half_plus': '1.5707963267948967', 'pi_minus': '3.14159265358979324'}[name]
        claim = up((value(es) * Fraction(8, 10) + 2 * DW_ACC + DW_ADD_F) * Fraction(101, 100) * 2)
        certs[f'{name}.g'] = rf"""# The form {label} (docs/atan2.md, section 3): y = (C {sign} F)(1 + ea) with C
# the double-word constant (relative error eC <= 2^-107; for pi, twice pi/2's, exact),
# F the fast value phi (1 + eF), eF within {es} (the largest of formal/atan2/compose_*.g and
# series_compose.g plus the ratio's 2^-104, section 3), against the angle A = C {sign} phi.
# ea: AccurateDWPlusDW, 3u^2/(1 - 4u) (docs/double-word.md). Written by
# generators/atan2_certificates.py.

A = C {sign} phi;
y = (C * (1 + eC) {sign} phi * (1 + eF)) * (1 + ea);

{{ C in [{const}, {const_hi}] /\ phi in [0, 0.7853981633974484] /\ A in [{c_lo}, {c_hi}]
  /\ eC in [-{lit(DW_ACC)}, {lit(DW_ACC)}] /\ {sym('eF', es)} /\ ea in [-{DW_ADD}, {DW_ADD}]
  -> (y - A) / A in [-{claim}, {claim}] }}

(y - A) / A -> ((C * eC {sign} phi * eF) * (1 + ea)) / A + ea {{ A <> 0 }};
"""
    return certs


def newton_certificate(phi_claim):
    """The accurate path's cubic step (section 5), relative to phi*."""
    eps_lit = up(phi_claim)
    e = value(eps_lit)
    exr = '1b-196'
    er = '1b-251'
    tr = '1b-254'
    cubic = Fraction(1001, 3000) * e * e * e
    bound = up(cubic + value(exr) + (cubic + e + value(exr)) * value(er) + Fraction(2, 2**254))
    text = rf"""# The accurate path's Newton step for d sin(phi) = n cos(phi) in Q256 (docs/atan2.md,
# section 5): phi_0 = phi* (1 + eps), |eps| <= {eps_lit}, delta = eps phi*. With R =
# sqrt(n^2 + d^2) the numerator is -R sin(delta) and the denominator R cos(delta),
# so the exact step is phi_0 - tan(delta) = phi* + delta - tan(delta), and
# tan(delta) = delta + c3 delta^3 / 3 with c3 in [0, 1.001] (|delta| <= 2^-52). The
# computed correction adds ex = phi* exr, the error of the Q256 sine and cosine
# (relative 2^-198, formal/trig/accurate_*.g) carried through n cos - d sin over
# d cos + n sin: at most 2^-197 n/(0.7 d) <= 2^-196.5 t <= 2^-196 phi*
# (t/atan t <= 4/pi); er the product's and the reciprocal's error relative to
# the correction (formal/trig/recip_3.g: 2^-252.6; the product 2^-255); tr the last
# sum. Written by generators/atan2_certificates.py.

delta = eps * phistar;
q3 = c3 * delta * delta * delta / 3;
phinew = (phistar * (1 + eps) + (-(delta + q3) + phistar * exr) * (1 + er)) * (1 + tr);

{{ phistar in [1b-900, 0.7853981633974484] /\ {sym('eps', eps_lit)} /\ c3 in [0, 1.001]
  /\ {sym('exr', exr)} /\ {sym('er', er)} /\ {sym('tr', tr)}
  -> (phinew - phistar) / phistar in [-{bound}, {bound}] }}

(phinew - phistar) / phistar -> ((-(c3 * eps * eps * eps * phistar * phistar / 3) + exr
    - (eps + c3 * eps * eps * eps * phistar * phistar / 3) * er + exr * er)
  + (1 - (c3 * eps * eps * eps * phistar * phistar / 3) + exr
    - (eps + c3 * eps * eps * eps * phistar * phistar / 3) * er + exr * er) * tr) {{ phistar <> 0 }};
"""
    return text, bound


def generate():
    d = atan2_constants.derive()
    values = d['values']
    out = {}
    claims = {}
    worst = Fraction(0)
    for k in range(1, atan2_constants.SEGMENTS + 1):
        row = d['rows'][k - 1]
        bound = eval_bound(row)
        text, dg = ac.eval_certificate(k, row, bound)
        out[f'eval_{k:02d}.g'] = text.replace('docs/asin.md', 'docs/atan2.md').replace(
            'asin_certificates.py', 'atan2_certificates.py')
        text, claim = compose_certificate(k, row, d, bound)
        out[f'compose_{k:02d}.g'] = text
        worst = max(worst, claim)
    out['series_tail.g'] = series_tail_certificate(values)
    text, series_claim = series_compose_certificate(values)
    out['series_compose.g'] = text
    series_value = value(series_claim)
    phi = max(worst, series_value)
    out['divide.g'] = divide_certificate()
    phi_total = phi + EPS_T
    out.update(form_certificates(phi_total))
    text, accurate = newton_certificate(phi_total)
    out['newton.g'] = text
    assert phi_total <= FAST * 9 / 10, f'phi bound 2^{math.log2(phi_total):.2f} exceeds 0.9 * 2^-63'
    assert value(accurate) <= Fraction(1, 2**189), f'accurate bound {float(value(accurate))}'
    return out, {'phi': phi_total, 'accurate': value(accurate)}


def main():
    files, claims = generate()
    DIR.mkdir(parents=True, exist_ok=True)
    if '--check' in sys.argv[1:]:
        for name, text in files.items():
            if (DIR / name).read_text() != text:
                sys.exit(f'{DIR / name} differs from a fresh generation')
        return
    for name, text in files.items():
        (DIR / name).write_text(text)
    print(f"{len(files)} certificates; phi 2^{math.log2(claims['phi']):.2f}, "
          f"accurate 2^{math.log2(claims['accurate']):.1f}")


if __name__ == '__main__':
    main()
