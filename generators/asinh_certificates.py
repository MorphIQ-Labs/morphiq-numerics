#!/usr/bin/env python3
"""Writes the Gappa certificates of asinh's fast path (docs/asinh.md) into
formal/asinh.

No number in a certificate is typed by hand: coefficients are the generated
tables' (generators/asinh_constants.py), the polynomial error is Sollya's
(generators/asinh_poly.out), and every other hypothesis is a bound certified
elsewhere (named where it is used) or derived here in exact rational
arithmetic, widened by at least 1% (`up`).

- series_tail.g and series_compose.g: the series below 2^-7 against asinh z,
  relative.
With --check, fails if the committed certificates differ from a fresh
generation. Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import asinh_constants  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/asinh'
T_LIT = '0.0078126'
DW_ADD = '776b-114'  # add and sub: 3u^2/(1 - 4u), widened (docs/double-word.md)
DW_ADD_F = Fraction(776, 2**114)
FAST = Fraction(1, 2**63)  # eps1 of the rounding test (docs/asinh.md section 5)


def frac(v):
    if isinstance(v, Fraction):
        return v
    import mpmath
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


def series_tail_certificate(values):
    """The series' tail zh^3 Q(zh^2) in binary64 against the polynomial
    evaluated exactly, relative. asinh z = z - z^3 Q(z^2), Q = q0 - s (q1 - s (q2
    - s q3)) with every q_j positive; the kernel's P = -Q operation for operation,
    rounding being odd."""
    q = [values[f'p00{j}'].lstrip('-') for j in range(4)]
    return f"""# The series' cubic term (docs/asinh.md, section 3): with zh a binary64,
# 2^-26 <= zh <= {T_LIT},
#   u = RN(zh^2), p = q0 - u (q1 - u (q2 - u q3)), tail = RN(RN(zh u) p)
# against zh^3 Q(zh^2), Q the same polynomial evaluated exactly. The kernel
# evaluates P = -Q with the signs of the coefficients, which is the same
# operations negated (rounding to nearest is odd). Each subtraction's second
# term is at most 2^-13 of the first, so every operation is a relative one.
# Written by generators/asinh_certificates.py.

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

{{ zh_ in [1b-26, {T_LIT}] -> (tail - Tx) / Tx in [-1b-51, 1b-51] }}

(tail - Tx) / Tx -> (1 + (a3 - zh * zh * zh) / (zh * zh * zh)) * (1 + (ps - P) / P) * (1 + (tail - a3 * ps) / (a3 * ps)) - 1
  {{ Tx <> 0, zh <> 0, P <> 0, a3 <> 0, ps <> 0 }};
(a3 - zh * zh * zh) / (zh * zh * zh) -> (1 + (uh - zh * zh) / (zh * zh)) * (1 + (a3 - zh * uh) / (zh * uh)) - 1
  {{ zh <> 0, uh <> 0 }};
"""


def series_compose_certificate(values):
    """The series' fast result against asinh z (section 3), relative."""
    rc = Fraction(11, 10**6)  # (z - asinh z)/z <= z^2/6 <= 1.02e-5 on z <= T
    eps = Fraction(1, 2**50)
    parts = Fraction(1, 2**51) + Fraction(1, 2**54) * (1 + Fraction(1, 2**23)) + Fraction(31, 10) * Fraction(1, 2**53)
    assert parts <= eps, 'the series eps pieces exceed 2^-50'
    claim = up(rc * eps * (1 + DW_ADD_F) + DW_ADD_F)
    return rf"""# The series' fast result (docs/asinh.md, section 3): F = (z - c)(1 + ea) with
# c = -RN(RN(z u) p) = RN(RN(z u) |p|) (the cubic term, positive), against
# A = asinh z = z (1 - rc), relative. rc = (z - asinh z)/z <= z^2/6 <= 1.1e-5 on
# z <= {T_LIT}; c differs from z - A by the relative eps, at most 2^-50: the
# tail's 2^-51 (formal/asinh/series_tail.g), Sollya's 2^-54 (1 + 2^-23) for the
# polynomial (asinh_poly.out) and 3.1 2^-53 for the rounding of z^2 inside
# z^3 Q(z^2); generators/asinh_certificates.py asserts their sum is at most
# 2^-50. ea: add_f64, 2u^2 (docs/double-word.md). Written by
# generators/asinh_certificates.py.

A = z * (1 - rc);
F = (z * (1 - rc * (1 + eps))) * (1 + ea);

{{ z in [1b-26, {T_LIT}] /\ rc in [0, 1.1e-5] /\ eps in [-1b-50, 1b-50] /\ ea in [-1b-104, 1b-104]
  -> (F - A) / A in [-{claim}, {claim}] }}

(F - A) / A -> ea - (rc * eps * (1 + ea)) / (1 - rc) {{ z <> 0, 1 - rc <> 0 }};
""", claim


def root_certificate():
    """s = sh + sl against the true root w of u (section 3), relative."""
    return rf"""# The logarithmic form's square root as a double-word (docs/asinh.md, section 3):
# u = uh + ul is the double-word 1 + x^2 (uh = RN(uh + ul), so |ul| <= 2^-53 uh),
# U = uh + ul = w^2 its exact value, root a binary64 with e = root - w, |e| <=
# 2^-51 (root = RN(sqrt(uh)), sqrt(uh) within 2^-54 of w relatively, the rounding
# of root at most 2^-52), (ph, pl) = two_prod(root, root) so ph + pl = root^2 and
# |pl| <= 2^-53 ph, r1 = uh - ph, r2 = r1 - pl, r3 = r2 + ul, corr = r3/(2 root),
# s = root + corr exactly (two_sum). Each of r1, r2, r3 and corr is one binary64
# operation, a relative error a1..a4 of at most 2^-53 (every value is normal). With
# e = root - w, U - root^2 = -e (root + w), so root + (U - root^2)/(2 root) - w =
# e^2/(2 root); the other terms are the four roundings. Every operation commutes
# with scaling u by 4^k (no subnormal or overflow for w between 1 and 2^29), so
# w in [1, 2] covers every w the logarithmic form reaches. Written by
# generators/asinh_certificates.py.

w = w_;
root = w + e;
uh = (w * w) / (1 + ulr);
ul = uh * ulr;
ph = (root * root) / (1 + plr);
pl = ph * plr;
r1 = (uh - ph) * (1 + a1);
r2 = (r1 - pl) * (1 + a2);
r3 = (r2 + ul) * (1 + a3);
s2 = 2 * root;
corr = (r3 / s2) * (1 + a4);
sv = root + corr;

{{ w_ in [1, 2] /\ e in [-1b-51, 1b-51] /\ ulr in [-1b-53, 1b-53] /\ plr in [-1b-53, 1b-53]
  /\ a1 in [-1b-53, 1b-53] /\ a2 in [-1b-53, 1b-53] /\ a3 in [-1b-53, 1b-53] /\ a4 in [-1b-53, 1b-53]
  -> (sv - w) / w in [-1b-100, 1b-100] }}

uh - ph -> -ul - e * (w + root) + pl {{ 1 + ulr <> 0, 1 + plr <> 0 }};
(sv - w) / w -> (e * e / s2 + (uh - ph) * a1 / s2 + (r1 - pl) * a2 / s2 + (r2 + ul) * a3 / s2 + r3 * a4 / s2) / w {{ w <> 0, root <> 0, 1 + ulr <> 0, 1 + plr <> 0 }};
"""


# The square root's bound with the double-word u's own error (2u^2 relative,
# halved by the root) added: root.g's 2^-100 + 2^-106.
ES = '1b-99'
# The double-word additions' bound for add_f64 (DWPlusFP): 2u^2.
DW_ADDF = '1b-104'


def log_certificate():
    """y = ln(vh) + RN(vl/vh) against asinh x (section 3), relative."""
    return rf"""# The logarithmic form's result (docs/asinh.md, section 3): A = asinh x = ln V,
# V = x + S, S = sqrt(x^2 + 1). The double-word v = (x + s)(1 + ev) with s from
# formal/asinh/root.g, so v = V (1 + ew), |ew| <= 2^-99 + 2^-105 (S/V <= 1; ES
# in the generator); Av = ln v = A + dw, |dw| <= 1.0001 |ew| <= 2^-98. vh = RN(v), vl = v - vh, d = ln(v/vh) =
# ln(1 + vl/vh), |d| <= 2^-52, and c = RN(vl/vh) satisfies |c - d| <= 1.5 2^-106
# (the rounding of the quotient and the quadratic term of ln(1 + t)). ln vh = Av - d
# from ln's fast value, within 2^-64 relatively (formal/ln/fast_a.g, fast_b.g
# and fast_c.g; docs/ln.md section 4), so L = (Av - d)(1 + eL), and
# y = (L + c)(1 + ea) with ea, add_f64's 2u^2 (docs/double-word.md). A is at
# least asinh(2^-7) > 0.0077. Written by generators/asinh_certificates.py.

A = a_;
Av = A + dw;
y = (((Av - d) * (1 + eL)) + d + cd) * (1 + ea);

{{ a_ in [0.0077, 21] /\ dw in [-1b-98, 1b-98] /\ d in [-1b-52, 1b-52] /\ cd in [-1b-105, 1b-105]
  /\ eL in [-1b-64, 1b-64] /\ ea in [-{DW_ADDF}, {DW_ADDF}]
  -> (y - A) / A in [-1b-63, 1b-63] }}

(y - A) / A -> (dw + (A + dw - d) * eL + cd + ((A + dw) + (A + dw - d) * eL + cd) * ea) / A {{ A <> 0 }};
"""


def large_certificate():
    """y = ln x + ln 2 + 1/(4x^2) against asinh x (section 3), relative."""
    return rf"""# The large form's result (docs/asinh.md, section 3): A = asinh x = ln x + ln 2
# + t4 + r, t4 = 1/(4x^2) <= 2^-58 and |r| <= 2^-114 (r = -3 t^2/32 + ..., t =
# 1/x^2 <= 2^-56). Lx = ln x (1 + eL), eL within 2^-64 (formal/ln/fast_*.g); LN2 is
# the double-word ln 2 within 2^-109 (generators/asinh_constants.py); the sum
# is a double-word addition (3u^2/(1 - 4u), docs/double-word.md), and c =
# RN(RN(1/4x)/x) differs from t4 by at most 2^-110 absolutely (the relative
# 2^-52 of 2^-58, and the underflow of c for x near 2^1024, below 2^-1074
# absolutely); the last addition is add_f64 (2u^2). Written by
# generators/asinh_certificates.py.

Ax = ax_;
A = Ax + l2 + t4 + r;
y = (((Ax * (1 + eL)) + l2 * (1 + e2)) * (1 + ea1) + t4 + ec) * (1 + ea2);

{{ ax_ in [19, 710.5] /\ l2 in [0.6931471805599453, 0.6931471805599454] /\ t4 in [0, 1b-58]
  /\ r in [-1b-114, 1b-114] /\ eL in [-1b-64, 1b-64] /\ e2 in [-1b-109, 1b-109]
  /\ ea1 in [-{DW_ADD}, {DW_ADD}] /\ ec in [-1b-110, 1b-110] /\ ea2 in [-{DW_ADDF}, {DW_ADDF}]
  -> (y - A) / A in [-1b-63, 1b-63] }}

(y - A) / A -> ((Ax * eL + l2 * e2) + (Ax * (1 + eL) + l2 * (1 + e2)) * ea1 + ec - r
  + ((Ax * (1 + eL) + l2 * (1 + e2)) * (1 + ea1) + t4 + ec) * ea2) / A {{ A <> 0 }};
"""


LEVEL_U = Fraction(1, 2**255)
R_MAX = Fraction(3467, 10000)  # |r| bound of the exponential's reduced argument
Y_MIN_LIT = '1b-27'            # asinh x >= 2^-27 for every x the accurate path serves
Y_MAX = 711


def value(literal):
    n, e = literal.split('b-')
    return Fraction(int(n), 2 ** int(e))


def sym(name, literal):
    return f'{name} in [-{literal}, {literal}]'


def exp_series_certificates(n_terms):
    """The Q256 exponential series' levels: H_n = 1 + (r c_n) H_(n+1),
    H_(N+1) = 1, against X_n = 1 + r c_n X_(n+1) at the same r, |r| <= R_MAX,
    c_n = 1/n."""
    files = {}
    e_prev, prev = Fraction(0), '0'
    for n in range(n_terms, 0, -1):
        c = Fraction(1, n)
        g_max = Fraction(142, 100) + e_prev
        bound = up(R_MAX * c * (e_prev + g_max * 3 * LEVEL_U) + 4 * LEVEL_U)
        files[f'exp_level_{n:02}.g'] = rf"""# Level {n} of the exponential's Q256 series (docs/asinh.md, section 4):
# H_{n} = 1 + (r c) H_{n + 1} against X_{n} = 1 + r c X_{n + 1}, c = 1/{n},
# given |H_{n + 1} - X_{n + 1}| <= {prev}. Q256 products are truncated toward zero
# (relative [-2^-255, 0]), the constant c is within 2^-255 relatively, and a sum
# is within 2^-254 of its larger operand (here at most 1.42: 2^-253).
# Written by generators/asinh_certificates.py.

Hn = Xn + En;
b = ((r * (1 / {n}) * (1 + kk)) * (1 + ma)) * Hn * (1 + mb);
H = 1 + b + sa;
X = 1 + r * (1 / {n}) * Xn;

{{ r in [-0.3467, 0.3467] /\ Xn in [0.7, 1.42]
  /\ {sym('En', prev)}
  /\ kk in [-1b-255, 1b-255] /\ ma in [-1b-255, 0] /\ mb in [-1b-255, 0] /\ sa in [-1b-253, 1b-253]
  -> H - X in [-{bound}, {bound}] }}

H - X -> (r * (1 / {n})) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + sa;
"""
        prev, e_prev = bound, value(bound)
    return files, e_prev


def exp_certificate(e_series):
    """e^y = m 2^k, m = exp r, against e^y (section 4), relative."""
    # r = y - k ln 2 in Q256: the constant within 2^-258 relatively, k L
    # truncated (2^-255 of |k L| <= 711), the sum within 2^-254 of its larger
    # operand (<= 711); so |dr| <= 711 (2^-258 + 2^-255 + 2^-254) absolutely.
    dr = up(Fraction(Y_MAX) * (Fraction(1, 2**258) + Fraction(1, 2**255) + Fraction(1, 2**254)))
    trunc = Fraction(1, 2**262)
    h = up(e_series + trunc)
    dx = up(value(dr) * Fraction(1001, 1000))
    eta = up((value(h) / Fraction(7, 10)) * (1 + value(dx)) + value(dx))
    text = rf"""# The exponential's accurate value (docs/asinh.md, section 4): m = H_1 against
# exp r for the reduced r = y - k ln 2 of the exact y. H_1 is within E1 of the exact
# series value X1 = exp(r_c) at the computed r_c (the levels' error and the
# truncated tail, 2^-262); r_c = r + dr with |dr| <= 711 (2^-258 + 2^-255 +
# 2^-254) (the Q256 constant ln 2, the truncated product k L, the sum); and
# exp(r_c)/exp(r) = 1 + dx with |dx| <= 1.001 |dr| (mean value theorem, e^|dr|).
# Written by generators/asinh_certificates.py.

Y = (1 + E1 / X1) * (1 + dx);

{{ X1 in [0.7, 1.42] /\ {sym('E1', h)} /\ {sym('dx', dx)}
  -> Y - 1 in [-{eta}, {eta}] }}
"""
    return text, eta


def newton_certificate(step, eps_lit, eta):
    """One Newton step for sinh y = x in Q256 (section 4), relative to the
    root y*: from y_0 = y* (1 + eps) the exact step is y* + q, q = c2 (eps y*)^2/2
    with c2 = sinh(xi)/cosh(y_0) in [0, 1.001]; the computed residual and
    division add ex (absolute), the correction er (relative to itself), the last
    sum tr (relative)."""
    e = value(eps_lit)
    ex = up(value(eta) * Fraction(1001, 1000))
    er = '1b-251'
    tr = '1b-254'
    bound = up(Fraction(1001, 2000) * e * e * Y_MAX + value(ex) / value(Y_MIN_LIT)
               + (Fraction(1001, 2000) * e * e * Y_MAX + e + value(ex) / value(Y_MIN_LIT)) * value(er)
               + Fraction(2, 2**254))
    text = rf"""# Newton step {step} for sinh y = x in Q256 (docs/asinh.md, section 4): y_0 = y* (1 +
# eps), |eps| <= {eps_lit}; the exact step lands at y* + q with q = c2 (eps y*)^2 / 2,
# c2 = sinh(xi)/cosh(y_0) in [0, 1.001] (xi between y_0 and y*, |xi - y_0| <=
# 2^-52); the computed correction is (q - eps y* + ex)(1 + er) with ex the sinh and
# cosh error (absolute, at most {ex}: the exponential's {eta}, formal/asinh/
# exp.g, with the sums' truncations) and er the product's and the reciprocal's
# error (formal/trig/recip_3.g: 2^-252.6; the product 2^-255); the last sum adds tr.
# Written by generators/asinh_certificates.py.

q = c2 * (eps * ystar) * (eps * ystar) / 2;
ynew = (ystar * (1 + eps) + (q - eps * ystar + ex) * (1 + er)) * (1 + tr);

{{ ystar in [{Y_MIN_LIT}, {Y_MAX}] /\ {sym('eps', eps_lit)} /\ c2 in [0, 1.001]
  /\ {sym('ex', ex)} /\ {sym('er', er)} /\ {sym('tr', tr)}
  -> (ynew - ystar) / ystar in [-{bound}, {bound}] }}

(ynew - ystar) / ystar -> ((q + ex + (q - eps * ystar + ex) * er)
  + (ystar + q + ex + (q - eps * ystar + ex) * er) * tr) / ystar {{ ystar <> 0 }};
"""
    return text, bound


def generate():
    d = asinh_constants.derive()
    values = d['values']
    out = {}
    out['series_tail.g'] = series_tail_certificate(values)
    text, series_claim = series_compose_certificate(values)
    out['series_compose.g'] = text
    out['root.g'] = root_certificate()
    out['log.g'] = log_certificate()
    out['large.g'] = large_certificate()
    levels, e_series = exp_series_certificates(d['n'])
    out.update(levels)
    text, eta = exp_certificate(e_series)
    out['exp.g'] = text
    eps = '1b-63'
    for step in (1, 2):
        text, bound = newton_certificate(step, eps, eta)
        out[f'newton_{step}.g'] = text
        eps = bound
    accurate = value(eps)
    assert accurate <= Fraction(1, 2**210), f'accurate path bound {float(accurate)} exceeds 2^-210'
    return out, {'series': series_claim, 'accurate': eps, 'exp': eta}


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
    print(f'{len(files)} certificates; claims {claims}')


if __name__ == '__main__':
    main()
