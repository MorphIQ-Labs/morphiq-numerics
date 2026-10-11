#!/usr/bin/env python3
"""Writes the Gappa certificates of ln_1p's stages H and B (docs/ln.md,
section 7) into formal/ln, and formal/ln/Ln1pCertificates.v, which states
each certificate's theorem over the reals through the Coq proof Gappa writes
for it.

No number in a certificate is typed by hand except a few goals of the
floating-point evaluations (stated below with the bound Gappa proves, each
at least 1% above it). The polynomials and their approximation bounds come
from generators/ln_poly.out (generators/ln_poly.sollya); the table bounds from
generators/ln1p_constants.py; every other hypothesis is derived below, and
each composed goal is the sum of its terms' bounds widened by at least 1%
(`up`), so Gappa proves it by interval arithmetic. A goal one certificate
proves is the hypothesis the next assumes. The constants the code uses
(crates/morphiq-numerics/src/ln/stages.rs) are checked against the goals by
formal/ln/Ln1pStageH.v and Ln1pStageB.v, with the margins the rounding test
needs.

With --check, fails if the committed files differ from a fresh generation.
Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import ln1p_constants as tables  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / 'formal/ln'
U = Fraction(1, 2**53)
Z_MAX = Fraction(1, 2**9)  # |z| <= 2^-9 (tables.Z_MAX)

# Goals of the floating-point evaluations: Gappa's bound, and the goal (>= 1% above).
H_Q = '577b-61'  # |(q - z^2 P(z)) / z^2|: Gappa 2^-51.998
H_PZ = ('-513b-10', '-511b-10')  # P(z) on |z| <= 2^-9: Gappa [-0.500652, -0.499349]
H_LRT_ERR = '1b-104'  # |lrt - L (1 - z)|: Gappa 2^-104.414
B_TAIL = '655b-62'  # |(tail - x^3 W(x)) / x^3|, |x| < 2^-9: Gappa 2^-52.674
B_W = ('681b-11', '684b-11')  # W(x) on |x| <= 2^-9: Gappa [0.332844, 0.333822]
B_LO = '830b-89'  # |lo - Ideal|, stage B's table branch: Gappa 2^-79.329


def value(literal):
    m, e = literal.split('b-')
    return Fraction(int(m), 2 ** int(e))


def up(v):
    """A literal m * 2^-e, m < 2^10, at least 1% above |v|."""
    v = abs(Fraction(v)) * Fraction(101, 100)
    e = -math.floor(math.log2(v)) + 9
    return f'{math.ceil(v * 2**e)}b-{e}'


def hex_fraction(text):
    sign = -1 if text.startswith('-') else 1
    mantissa, exponent = text.lstrip('-')[2:].split('p')
    whole, _, fraction = mantissa.partition('.')
    digits = int(whole + fraction, 16)
    return sign * Fraction(digits) * Fraction(2) ** (int(exponent) - 4 * len(fraction))


def poly():
    values = dict(line.split() for line in tables.POLY.read_text().split('\n') if line.strip())
    return values


def sym(name, literal):
    return f'{name} in [-{literal}, {literal}]'


def coq_r(literal):
    """A literal m b-e as a Coq real."""
    m, e = literal.split('b-')
    return f'{m} * / 2 ^ {e}'


def coq_neg(literal):
    """A literal -m b-e as a Coq real."""
    return f'- ({coq_r(literal.lstrip("-"))})'


def derive():
    p = poly()
    h = [p[f'h{k}'] for k in range(3, 7)]
    b = [p[f'b{k}'] for k in range(3, 9)]
    rho_h = hex_fraction(p['h_relative_error_bound'])
    rho_b = hex_fraction(p['b_relative_error_bound'])
    hv = [hex_fraction(c) for c in h]
    bv = [hex_fraction(c) for c in b]
    # max |Q| on |z| <= 2^-9, coefficient by coefficient
    q_h = sum(abs(c) * Z_MAX**k for k, c in enumerate(hv))
    q_b = sum(abs(c) * Z_MAX**k for k, c in enumerate(bv))
    d = {}
    d['h'], d['b'] = h, b
    # ln(1 + z) - z - z^2 P(z) = (ln(1 + z) - z + z^2/2 - z^3 Q(z)), at most
    # rho |z^3 Q(z)| <= rho 2^-9 max|Q| z^2 (Sollya's supnorm, relative).
    d['h_approx'] = up(rho_h * Z_MAX * q_h)
    # stage B: at most rho |z|^3 max|Q|.
    d['b_approx'] = up(rho_b * q_b)
    # |L| = |l| R 2^-E <= 2^-53 h R 2^-E = 2^-53 (1 + z) <= 2^-53 (1 + 2^-9).
    lm = up(U * (1 + Z_MAX))
    d['L'] = lm
    d['lrt'] = up(value(lm) * (1 + Z_MAX) * (1 + U) ** 3 + value(H_LRT_ERR))
    # u = L / (1 + z): |ln(1 + u) - u| <= u^2 / (1 - |u|).
    um = value(lm) / (1 - Z_MAX)
    d['t6'] = up(um * um / (1 - um))
    # Stage H's ratios to |s|: E = 0 with R != 1 (|s| >= s_min), and E != 0
    # (|s| >= (L1_min - TH_max - 2^-9) |E| >= 0.3439 |E|).
    s_e = Fraction(3439, 10000)
    tau = max(tables.T_ERR / tables.S_MIN,
              (tables.L_ERR + U * tables.L0_MAX + tables.T_ERR) / s_e / (1 - U))
    kap = max(tables.TL_MAX / tables.S_MIN,
              2 * tables.L0_MAX * (1 + U) ** 3 / s_e / (1 - U))
    d['tau'], d['kap'] = up(tau), up(kap)
    # Gz, Gs, GA: the sums of their terms' bounds.
    t4, t3, pz = value(H_Q), value(d['h_approx']), abs(value(H_PZ[0].lstrip('-')))
    d['gz'] = up(t4 + t3 + value(lm) / (1 - Z_MAX) + U * (pz + t4))
    ta, ka, eta = value(d['tau']), value(d['kap']), U
    d['gs'] = up(ta + U * ka / (1 - U) + U * ka + U * (eta + ka * (1 + U)) + U * (1 + U) * (eta + ka * (1 + U)))
    t5, t6, lr = value(H_LRT_ERR), value(d['t6']), value(d['lrt'])
    d['ga'] = up(t5 + t6 + U * lr + U * lr * (1 + U) + U * (1 + U) ** 2 * lr)
    # Stage B's small branch: err = x^3 Gx3 + x Gx1, |x| <= 2^-9.
    w_hi = value(B_W[1])
    pi = up(U * (1 + U))  # |pl| <= 2^-53 x^2 (1 + u): two_prod's error
    eta_b = up(U * (1 + Z_MAX))  # |e1| <= 2^-53 |s| <= 2^-53 (1 + 2^-9) |x|
    d['pi'], d['eta_b'] = pi, eta_b
    ap, tb = value(d['b_approx']), value(B_TAIL)
    d['gx3'] = up(ap + tb + U * (w_hi + tb) + U * (1 + U) * (w_hi + tb))
    d['gx1'] = up(Z_MAX * (U + U * (1 + U)) * value(pi) / 2 + U * value(eta_b))
    # Stage B's table branch: the reduction's error (|E| <= 1020, |ln0| <= 2^-34),
    # the approximation (rho |z|^3 max|Q| <= rho max|Q| 2^-27), the l term
    # (u^2/(1 - |u|) + |L| z^4 / (1 - |z|)), and lo's evaluation.
    t1 = 1020 * tables.L_ERR + tables.T_ERR + U * 1020 * tables.L0_MAX + U * Fraction(1, 2**34) / (1 - U)
    d['b_t1'] = up(t1)
    d['b_ap'] = up(ap * Z_MAX**3)
    d['b_lt'] = up(t6 + value(lm) * Z_MAX**4 / (1 - Z_MAX))
    d['b_total'] = up(value(d['b_t1']) + value(d['b_ap']) + value(d['b_lt']) + value(B_LO))
    return d


def stage_h_q(d):
    h3, h4, h5, h6 = d['h']
    return f'''# ln_1p's stage H (docs/ln.md, section 7): the polynomial P(z) = -1/2 + z Q(z),
# evaluated by Estrin's scheme with every operation rounded to binary64,
# nearest-even, as crates/morphiq-numerics/src/ln/stages.rs does, and
# q = RN(RN(z^2) P), against z^2 P(z) evaluated exactly, relative to z^2.
# h3..h6 are generators/ln_poly.out's. Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

h3 = {h3};
h4 = {h4};
h5 = {h5};
h6 = {h6};

z2 = rnd(z * z);
t0 = rnd(rnd(z * h3) - 1b-1);
t1 = rnd(rnd(z * h5) + h4);
a1 = rnd(rnd(z2 * h6) + t1);
p = rnd(rnd(z2 * a1) + t0);
q = rnd(z2 * p);
Pz = z * z * (z * z * h6 + (z * h5 + h4)) + (z * h3 - 1b-1);

{{ |z| in [1b-62, 1b-9]
  -> (q - z * z * Pz) / (z * z) in [-{H_Q}, {H_Q}] /\\ Pz in [{H_PZ[0]}, {H_PZ[1]}] }}

(q - z * z * Pz) / (z * z) -> ((q - z2 * p) / (z2 * p)) * p * (z2 / (z * z)) + ((z2 - z * z) / (z * z)) * p + (p - Pz)
  {{ z <> 0, z2 * p <> 0 }};
z2 / (z * z) -> 1 + (z2 - z * z) / (z * z) {{ z <> 0 }};
'''


def stage_h_lr(d):
    return f'''# ln_1p's stage H (docs/ln.md, section 7): the l term, lrt = RN(RN(L) RN(1 - z))
# with L = l R 2^-E exact, |L| <= 2^-53 (1 + 2^-9), against L (1 - z), absolute.
# Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

lr = rnd(L);
omz = rnd(1 - z);
lrt = rnd(lr * omz);

{{ {sym('L', d['L'])} /\\ z in [-1b-9, 1b-9]
  -> lrt - L * (1 - z) in [-{H_LRT_ERR}, {H_LRT_ERR}] /\\ {sym('lrt', d['lrt'])} }}

lrt - L * (1 - z) -> (lrt - lr * omz) + (lr - L) * omz + L * (omz - (1 - z));
'''


def stage_h_gz(d):
    return f'''# ln_1p's stage H (docs/ln.md, section 7): the error terms proportional to z^2,
# over z^2. t4: q's evaluation (formal/ln/stage_h_q.g); t3: the approximation,
# |ln(1 + z) - z - z^2 P(z)| <= t3 z^2 (generators/ln_poly.sollya, proved in
# formal/ln/Ln1pApprox.v); L / (1 + z): from ln(1 + L/(1 + z)) - L (1 - z);
# d3: lo's rounding, times q / z^2. Written by generators/ln1p_certificates.py.

Gz = - t4 + t3 + L / (1 + z) - d3 * (Pz + t4);

{{ {sym('t4', H_Q)} /\\ {sym('t3', d['h_approx'])} /\\ {sym('L', d['L'])} /\\ z in [-1b-9, 1b-9]
  /\\ d3 in [-1b-53, 1b-53] /\\ Pz in [{H_PZ[0]}, {H_PZ[1]}]
  -> {sym('Gz', d['gz'])} }}
'''


def stage_h_gs(d):
    return f'''# ln_1p's stage H (docs/ln.md, section 7): the error terms proportional to |s|,
# over s. tau: the tables' and E ln 2's errors; kap = ln0 / s; eta = e1 / s,
# Fast2Sum's error; d0..d3: the roundings of ln0, w, pre and lo.
# Written by generators/ln1p_certificates.py.

Gs = tau - d0 * kap / (1 + d0) - d1 * kap - d2 * (eta + kap * (1 + d1)) - d3 * (1 + d2) * (eta + kap * (1 + d1));

{{ {sym('tau', d['tau'])} /\\ {sym('kap', d['kap'])} /\\ eta in [-1b-53, 1b-53]
  /\\ d0 in [-1b-53, 1b-53] /\\ d1 in [-1b-53, 1b-53] /\\ d2 in [-1b-53, 1b-53] /\\ d3 in [-1b-53, 1b-53]
  -> {sym('Gs', d['gs'])} }}
'''


def stage_h_ga(d):
    return f'''# ln_1p's stage H (docs/ln.md, section 7): the absolute error terms. t5: the
# l term (formal/ln/stage_h_lr.g); t6: ln(1 + u) - u, u = L / (1 + z);
# d1..d3: the roundings of w, pre and lo, times lrt.
# Written by generators/ln1p_certificates.py.

GA = - t5 + t6 - d1 * lrt - d2 * lrt * (1 + d1) - d3 * (1 + d2) * lrt * (1 + d1);

{{ {sym('t5', H_LRT_ERR)} /\\ {sym('t6', d['t6'])} /\\ {sym('lrt', d['lrt'])}
  /\\ d1 in [-1b-53, 1b-53] /\\ d2 in [-1b-53, 1b-53] /\\ d3 in [-1b-53, 1b-53]
  -> {sym('GA', d['ga'])} }}
'''


def horner_rnd(var):
    return [f'w4 = rnd(rnd({var} * b8) + b7);', f'w3 = rnd(rnd({var} * w4) + b6);',
            f'w2 = rnd(rnd({var} * w3) + b5);', f'w1 = rnd(rnd({var} * w2) + b4);',
            f'w0 = rnd(rnd({var} * w1) + b3);']


def coefficients_b(d):
    return '\n'.join(f'b{k} = {c};' for k, c in zip(range(3, 9), d['b']))


def stage_b_small_tail(d):
    nl = '\n'
    return f'''# ln_1p's stage B, |x| < 2^-9 (docs/ln.md, section 7): the tail
# tail = RN(RN(x RN(x^2)) W), W = Q(x) by Horner's scheme rounded to binary64,
# against x^3 Q(x) evaluated exactly, relative to x^3; b3..b8 are
# generators/ln_poly.out's. Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

{coefficients_b(d)}

p = rnd(x * x);
xp = rnd(x * p);
{nl.join(horner_rnd('x'))}
tail = rnd(xp * w0);
W = x * (x * (x * (x * (x * b8 + b7) + b6) + b5) + b4) + b3;

{{ |x| in [1b-54, 1b-9]
  -> (tail - x * x * x * W) / (x * x * x) in [-{B_TAIL}, {B_TAIL}] /\\ W in [{B_W[0]}, {B_W[1]}] }}

(tail - x * x * x * W) / (x * x * x) -> ((tail - xp * w0) / (xp * w0)) * (xp / (x * x * x)) * w0
  + ((xp - x * x * x) / (x * x * x)) * w0 + (w0 - W) {{ x <> 0, xp * w0 <> 0 }};
xp / (x * x * x) -> 1 + (xp - x * x * x) / (x * x * x) {{ x <> 0 }};
(xp - x * x * x) / (x * x * x) -> ((xp - x * p) / (x * p)) * (p / (x * x)) + (p - x * x) / (x * x) {{ x <> 0, x * p <> 0 }};
p / (x * x) -> 1 + (p - x * x) / (x * x) {{ x <> 0 }};
xp -> (x * p) * (1 + (xp - x * p) / (x * p)) {{ x * p <> 0 }};
'''


def stage_b_small(d):
    return f'''# ln_1p's stage B, |x| < 2^-9 (docs/ln.md, section 7): the error over x^3 (Gx3)
# and over x (Gx1). al: the approximation, |ln(1 + x) - x + x^2/2 - x^3 W(x)|
# <= al |x|^3 (proved in formal/ln/Ln1pApprox.v); be: the tail's evaluation
# (formal/ln/stage_b_small_tail.g); pi = pl / x^2, two_prod's error; eta = e1 / x,
# Fast2Sum's error; d1, d2: the roundings of w and lo; m = x.
# Written by generators/ln1p_certificates.py.

Gx3 = al - be - d1 * (W + be) - d2 * (1 + d1) * (W + be);
Gx1 = m * (d1 + d2 * (1 + d1)) * pi / 2 - d2 * eta;

{{ {sym('al', d['b_approx'])} /\\ {sym('be', B_TAIL)} /\\ W in [{B_W[0]}, {B_W[1]}]
  /\\ {sym('pi', d['pi'])} /\\ {sym('eta', d['eta_b'])} /\\ m in [-1b-9, 1b-9]
  /\\ d1 in [-1b-53, 1b-53] /\\ d2 in [-1b-53, 1b-53]
  -> {sym('Gx3', d['gx3'])} /\\ {sym('Gx1', d['gx1'])} }}
'''


def stage_b_lo(d):
    nl = '\n'
    return f'''# ln_1p's stage B, |x| >= 2^-9 (docs/ln.md, section 7): the low word lo, every
# operation rounded to binary64 as crates/morphiq-numerics/src/ln/stages.rs
# does, against Ideal = e1 + e2 + ln0 + L (1 - z + z^2 - z^3) - pl/2 + z^3 Q(z).
# z binary64, |z| <= 2^-9; p + pl = z^2 exactly (two_prod); L = l R 2^-E exact,
# |L| <= 2^-53 (1 + 2^-9); e1, e2 the Fast2Sum errors, binary64, below 2^-44
# (|s| < 1024); ln0 binary64, |ln0| <= 2^-34 (|E| <= 1020). -0.5 pl is exact.
# Written by generators/ln1p_certificates.py.

@rnd = float<ieee_64, ne>;

{coefficients_b(d)}

p = rnd(z * z);
pl = z * z - p;
zp = rnd(z * p);
{nl.join(horner_rnd('z'))}
W = z * (z * (z * (z * (z * b8 + b7) + b6) + b5) + b4) + b3;
tail = rnd(zp * w0);
r1 = rnd(tail - pl / 2);
lr = rnd(L);
omz = rnd(1 - z);
aa = rnd(omz + p);
bb = rnd(aa - zp);
lrt = rnd(lr * bb);
r2 = rnd(ln0 + lrt);
r3 = rnd(r2 + r1);
r4 = rnd(e1 + e2);
lo = rnd(r4 + r3);
Ideal = e1 + e2 + ln0 + L * (1 - z + z * z - z * z * z) - pl / 2 + z * z * z * W;

{{ |z| in [1b-62, 1b-9] /\\ {sym('L', d['L'])}
  /\\ e1 in [-1b-44, 1b-44] /\\ e2 in [-1b-44, 1b-44] /\\ ln0 in [-1b-34, 1b-34]
  /\\ @FIX(e1, -1074) /\\ @FIX(e2, -1074) /\\ @FIX(ln0, -1074)
  -> lo - Ideal in [-{B_LO}, {B_LO}] /\\ lo in [-1b-28, 1b-28] }}

lo - Ideal -> (lo - (r4 + r3)) + (r4 - (e1 + e2)) + (r3 - (r2 + r1)) + (r2 - (ln0 + lrt)) + (r1 - (tail - pl / 2))
  + (tail - z * z * z * W) + (lrt - L * (1 - z + z * z - z * z * z));
lrt - L * (1 - z + z * z - z * z * z) -> (lrt - lr * bb) + (lr - L) * bb + L * (bb - (1 - z + z * z - z * z * z));
bb - (1 - z + z * z - z * z * z) -> (bb - (aa - zp)) + (aa - (omz + p)) + (omz - (1 - z)) + (p - z * z) - (zp - z * z * z);
tail - z * z * z * W -> (tail - zp * w0) + (zp - z * z * z) * w0 + z * z * z * (w0 - W);
zp - z * z * z -> (zp - z * p) + z * (p - z * z);
'''


def stage_b_total(d):
    return f'''# ln_1p's stage B, |x| >= 2^-9 (docs/ln.md, section 7): the total error,
# absolute. t1: the tables', E ln 2's and ln0's errors; ap: the approximation
# (formal/ln/Ln1pApprox.v); lt: ln(1 + z + L) - ln(1 + z) - L (1 - z + z^2 - z^3);
# g: lo's evaluation (formal/ln/stage_b_lo.g). Written by
# generators/ln1p_certificates.py.

Y = t1 + ap + lt - g;

{{ {sym('t1', d['b_t1'])} /\\ {sym('ap', d['b_ap'])} /\\ {sym('lt', d['b_lt'])} /\\ {sym('g', B_LO)}
  -> {sym('Y', d['b_total'])} }}
'''


def coq_const(hexval):
    """A binary64 constant as Gappa reads it: IZR m * bpow radix2 e, m odd."""
    v = hex_fraction(hexval)
    m, e = v.numerator, 0
    den = v.denominator
    while den > 1:
        den //= 2
        e -= 1
    while m % 2 == 0 and m != 0:
        m //= 2
        e += 1
    return f'IZR {m if m >= 0 else f"({m})"} * bpow radix2 ({e})'


def lit(literal):
    """A literal [-]m b-e as Gappa reads it."""
    neg = literal.startswith('-')
    m, e = literal.lstrip('-').split('b-')
    m, e = int(m), -int(e)
    while m % 2 == 0:
        m //= 2
        e += 1
    m = -m if neg else m
    return f'IZR {m if m >= 0 else f"({m})"} * bpow radix2 ({e})'


def rng(name, literal):
    return f'{lit("-" + literal)} <= {name} <= {lit(literal)}'


def rng2(name, lo, hi):
    return f'{lit(lo)} <= {name} <= {lit(hi)}'


COQ_HEAD = """(** The certificates of [ln_1p]'s stages H and B over reals (docs/ln.md,
    section 7), written by generators/ln1p_certificates.py with the same bounds
    it writes into formal/ln/stage_*.g; do not edit. Each theorem is its
    certificate's, applied through the Coq proof Gappa writes for it: [rn] is
    Gappa's binary64 rounding, nearest-even, and each constant is [m·2^e] as
    Gappa reads it. *)

From Coq Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Gappa Require Gappa_definitions Gappa_pred_bnd Gappa_round_def.
Require ln_stage_h_q ln_stage_h_lr ln_stage_h_gz ln_stage_h_gs ln_stage_h_ga
  ln_stage_b_small_tail ln_stage_b_small ln_stage_b_lo ln_stage_b_total.

Open Scope R_scope.

Notation rn := (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE).

(** Normalizes a certificate's statement and ours alike, keeping the
    rounding, the real operators and the constants' [IZR] and [bpow]. *)
Ltac gnorm := cbv beta iota zeta delta -[round radix2 FLT_exp Gappa_round_def.rndNE Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult].
Ltac gnorm_in H := cbv beta iota zeta delta -[round radix2 FLT_exp Gappa_round_def.rndNE Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult] in H.
Ltac gnorm_all := repeat match goal with H : _ |- _ => progress gnorm_in H end; gnorm.

(** A goal [lo <= g <= hi] from certificate [l1], one side at a time: assume
    it fails, so the certificate's hypotheses hold and its conclusion fails.
    [gbound] for a certificate with one conclusion, [gbound_l] and [gbound_r]
    for the first or second of two. *)
Ltac gconcl := let Hb := fresh "Hb" in
  intros Hb; gnorm_in Hb; match goal with H : _ < _ |- _ => gnorm_in H end; lra.
Ltac ghyps := gnorm_all; repeat split; first [assumption | lra].
Ltac gbound l1 := split; (apply Rnot_lt_le; intros ?; apply l1; split; [ghyps | gconcl]).
Ltac gbound_l l1 := split; (apply Rnot_lt_le; intros ?; apply l1; split; [ghyps | left; gconcl]).
Ltac gbound_r l1 := split; (apply Rnot_lt_le; intros ?; apply l1; split; [ghyps | right; gconcl]).
"""


def coq(d):
    h3, h4, h5, h6 = (coq_const(c) for c in d['h'])
    b = [coq_const(c) for c in d['b']]
    half = 'IZR 1 * bpow radix2 (-1)'
    one = lit('1b-53')
    out = [COQ_HEAD]
    out.append(f"""(** * Stage H *)

Definition h3 : R := {h3}.
Definition h4 : R := {h4}.
Definition h5 : R := {h5}.
Definition h6 : R := {h6}.

(** [P(z)] by Estrin's scheme, rounded as the code rounds it, and exactly. *)
Definition h_p (z : R) : R :=
  let z2 := rn (z * z) in
  let t0 := rn (rn (z * h3) - {half}) in
  let t1 := rn (rn (z * h5) + h4) in
  let a1 := rn (rn (z2 * h6) + t1) in
  rn (rn (z2 * a1) + t0).
Definition h_q (z : R) : R := rn (rn (z * z) * h_p z).
Definition h_Pz (z : R) : R := z * z * (z * z * h6 + (z * h5 + h4)) + (z * h3 - {half}).

(** formal/ln/stage_h_q.g. *)
Theorem stage_h_q z : {lit('1b-62')} <= Rabs z <= {lit('1b-9')} ->
  ({rng('(h_q z - z * z * h_Pz z) / (z * z)', H_Q)}) /\\
  ({rng2('h_Pz z', H_PZ[0], H_PZ[1])}).
Proof.
  intros Hz. unfold h_q, h_p, h_Pz, h3, h4, h5, h6.
  split; [gbound_l (ln_stage_h_q.l1 z) | gbound_r (ln_stage_h_q.l1 z)].
Qed.

(** formal/ln/stage_h_lr.g. *)
Theorem stage_h_lr L z : {rng('L', d['L'])} -> {rng('z', '1b-9')} ->
  ({rng('rn (rn L * rn (1 - z)) - L * (1 - z)', H_LRT_ERR)}) /\\
  ({rng('rn (rn L * rn (1 - z))', d['lrt'])}).
Proof.
  intros HL Hz.
  split; [gbound_l (ln_stage_h_lr.l1 L z) | gbound_r (ln_stage_h_lr.l1 L z)].
Qed.

(** formal/ln/stage_h_gz.g. *)
Theorem stage_h_gz t4 t3 L z d3 Pz : {rng('t4', H_Q)} -> {rng('t3', d['h_approx'])} ->
  {rng('L', d['L'])} -> {rng('z', '1b-9')} -> {rng('d3', '1b-53')} -> {rng2('Pz', H_PZ[0], H_PZ[1])} ->
  {rng('- t4 + t3 + L / (1 + z) - d3 * (Pz + t4)', d['gz'])}.
Proof. intros. gbound (ln_stage_h_gz.l1 t4 t3 L z d3 Pz). Qed.

(** formal/ln/stage_h_gs.g. *)
Theorem stage_h_gs tau kap eta d0 d1 d2 d3 : {rng('tau', d['tau'])} -> {rng('kap', d['kap'])} ->
  {rng('eta', '1b-53')} -> {rng('d0', '1b-53')} -> {rng('d1', '1b-53')} -> {rng('d2', '1b-53')} ->
  {rng('d3', '1b-53')} ->
  {rng('tau - d0 * kap / (1 + d0) - d1 * kap - d2 * (eta + kap * (1 + d1)) - d3 * (1 + d2) * (eta + kap * (1 + d1))', d['gs'])}.
Proof. intros. gbound (ln_stage_h_gs.l1 tau kap eta d0 d1 d2 d3). Qed.

(** formal/ln/stage_h_ga.g. *)
Theorem stage_h_ga t5 t6 lrt d1 d2 d3 : {rng('t5', H_LRT_ERR)} -> {rng('t6', d['t6'])} ->
  {rng('lrt', d['lrt'])} -> {rng('d1', '1b-53')} -> {rng('d2', '1b-53')} -> {rng('d3', '1b-53')} ->
  {rng('- t5 + t6 - d1 * lrt - d2 * lrt * (1 + d1) - d3 * (1 + d2) * lrt * (1 + d1)', d['ga'])}.
Proof. intros. gbound (ln_stage_h_ga.l1 t5 t6 lrt d1 d2 d3). Qed.

(** * Stage B *)

Definition b3 : R := {b[0]}.
Definition b4 : R := {b[1]}.
Definition b5 : R := {b[2]}.
Definition b6 : R := {b[3]}.
Definition b7 : R := {b[4]}.
Definition b8 : R := {b[5]}.

(** [W(v)] by Horner's scheme, rounded as the code rounds it, and exactly. *)
Definition b_w (v : R) : R :=
  let w4 := rn (rn (v * b8) + b7) in
  let w3 := rn (rn (v * w4) + b6) in
  let w2 := rn (rn (v * w3) + b5) in
  let w1 := rn (rn (v * w2) + b4) in
  rn (rn (v * w1) + b3).
Definition b_W (v : R) : R := v * (v * (v * (v * (v * b8 + b7) + b6) + b5) + b4) + b3.

(** formal/ln/stage_b_small_tail.g: [tail = RN(RN(x RN(x^2)) W)]. *)
Theorem stage_b_small_tail x : {lit('1b-54')} <= Rabs x <= {lit('1b-9')} ->
  ({rng('(rn (rn (x * rn (x * x)) * b_w x) - x * x * x * b_W x) / (x * x * x)', B_TAIL)}) /\\
  ({rng2('b_W x', B_W[0], B_W[1])}).
Proof.
  intros Hx. unfold b_w, b_W, b3, b4, b5, b6, b7, b8.
  split; [gbound_l (ln_stage_b_small_tail.l1 x) | gbound_r (ln_stage_b_small_tail.l1 x)].
Qed.

(** formal/ln/stage_b_small.g. *)
Theorem stage_b_small al be W pi eta m d1 d2 : {rng('al', d['b_approx'])} -> {rng('be', B_TAIL)} ->
  {rng2('W', B_W[0], B_W[1])} -> {rng('pi', d['pi'])} -> {rng('eta', d['eta_b'])} -> {rng('m', '1b-9')} ->
  {rng('d1', '1b-53')} -> {rng('d2', '1b-53')} ->
  ({rng('al - be - d1 * (W + be) - d2 * (1 + d1) * (W + be)', d['gx3'])}) /\\
  ({rng('m * (d1 + d2 * (1 + d1)) * pi / 2 - d2 * eta', d['gx1'])}).
Proof.
  intros.
  split; [gbound_l (ln_stage_b_small.l1 al be W pi eta m d1 d2) | gbound_r (ln_stage_b_small.l1 al be W pi eta m d1 d2)].
Qed.

(** [lo] of stage B's table branch, rounded as the code rounds it. *)
Definition b_lo (e1 e2 ln0 L z : R) : R :=
  let p := rn (z * z) in
  let pl := z * z - p in
  let zp := rn (z * p) in
  let tail := rn (zp * b_w z) in
  let r1 := rn (tail - pl / 2) in
  let lrt := rn (rn L * rn (rn (rn (1 - z) + p) - zp)) in
  let r2 := rn (ln0 + lrt) in
  let r3 := rn (r2 + r1) in
  let r4 := rn (e1 + e2) in
  rn (r4 + r3).
Definition b_ideal (e1 e2 ln0 L z : R) : R :=
  e1 + e2 + ln0 + L * (1 - z + z * z - z * z * z) - (z * z - rn (z * z)) / 2 + z * z * z * b_W z.

(** formal/ln/stage_b_lo.g. *)
Theorem stage_b_lo e1 e2 ln0 L z : {lit('1b-62')} <= Rabs z <= {lit('1b-9')} -> {rng('L', d['L'])} ->
  {rng('e1', '1b-44')} -> {rng('e2', '1b-44')} -> {rng('ln0', '1b-34')} ->
  Gappa_definitions.FIX e1 (-1074) -> Gappa_definitions.FIX e2 (-1074) -> Gappa_definitions.FIX ln0 (-1074) ->
  ({rng('b_lo e1 e2 ln0 L z - b_ideal e1 e2 ln0 L z', B_LO)}) /\\
  ({rng('b_lo e1 e2 ln0 L z', '1b-28')}).
Proof.
  intros. unfold b_lo, b_ideal, b_w, b_W, b3, b4, b5, b6, b7, b8.
  split; [gbound_l (ln_stage_b_lo.l1 e1 e2 ln0 L z) | gbound_r (ln_stage_b_lo.l1 e1 e2 ln0 L z)].
Qed.

(** formal/ln/stage_b_total.g. *)
Theorem stage_b_total t1 ap lt g : {rng('t1', d['b_t1'])} -> {rng('ap', d['b_ap'])} ->
  {rng('lt', d['b_lt'])} -> {rng('g', B_LO)} ->
  {rng('t1 + ap + lt - g', d['b_total'])}.
Proof. intros. gbound (ln_stage_b_total.l1 t1 ap lt g). Qed.
""")
    return ''.join(out)


def generate():
    d = derive()
    return {
        'stage_h_q.g': stage_h_q(d),
        'stage_h_lr.g': stage_h_lr(d),
        'stage_h_gz.g': stage_h_gz(d),
        'stage_h_gs.g': stage_h_gs(d),
        'stage_h_ga.g': stage_h_ga(d),
        'stage_b_small_tail.g': stage_b_small_tail(d),
        'stage_b_small.g': stage_b_small(d),
        'stage_b_lo.g': stage_b_lo(d),
        'stage_b_total.g': stage_b_total(d),
        'Ln1pCertificates.v': coq(d),
    }


def main():
    files = generate()
    check = '--check' in sys.argv[1:]
    if check:
        present = {p.name for p in DIR.glob('stage_*.g')}
        if present != {n for n in files if n.endswith('.g')}:
            sys.exit('formal/ln holds stage certificates this generator does not write')
    for name, text in files.items():
        path = DIR / name
        if check:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.write_text(text)


if __name__ == '__main__':
    main()
