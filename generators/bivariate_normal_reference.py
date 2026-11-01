#!/usr/bin/env python3
"""Independent bivariate-normal witnesses at 280 and 360 bits.

The reference is Plackett's identity written in Genz's angle,
P(X <= h, Y <= k; rho) = P(X <= h, Y <= k; -1)
    + 1/(2 pi) int_{-pi/2}^{asin rho} exp(-(h^2 + k^2 - 2 h k sin t) / (2 cos^2 t)) dt,
evaluated by tanh-sinh quadrature with mpmath on the exact binary64 inputs.
No library code and no Genz or Drezner-Wesolowsky rule is called. Where
h + k > 0 the survival identity P(h, k) = 1 - Phi(-h) - Phi(-k) + P(-h, -k)
moves the integral to the side where P(-1) = 0, so the integrand is positive
and no cancellation reaches a small probability: the value is then accurate in
relative terms as well as absolutely.

Every case is evaluated at two precisions and must agree to 1e-36 relative
(or 1e-46 absolute; the `deep` cases, down to 1e-290, to 1e-30 relative); a subset is also evaluated by a second route, Owen's
T function, which shares no integrand with the first, and must agree with the
first to 1e-30 absolute. Every `deep` case is instead evaluated by Plackett's
identity, a positive integral over the correlation, and must agree to 1e-28 relative. The value is written with 36 significant digits.
Replay with --check.
"""
import math
import json
import os
import pathlib
import sys
import time
from multiprocessing import Pool

import mpmath as mp
from oracle import from_bits, splitmix64, to_bits

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'crates/reference/fixtures/bivariate_normal.json'

PRECISIONS = (280, 360)
DIGITS = 36
RULE_LIMITS = (0.20, 0.29, 0.66, 0.75, 0.89)
ONE_MINUS = [2.0 ** -k for k in (20, 30, 40, 50, 52)]
RHOS = sorted({
    0.0, 2.0 ** -40, 2.0 ** -20, 0.01, 0.09, 0.0900000000000001, 0.1, 0.3, 0.3000000000000001,
    0.5, 0.65, 0.7, 0.75, 0.7500000000000001, 0.8, 0.9, 0.92, 0.925, 0.9250000000000002,
    0.93, 0.95, 0.99, 0.999, *(1.0 - e for e in ONE_MINUS),
    # Each rule limit (docs/bivariate_normal.md section 4) at adjacent doubles.
    *(v for limit in RULE_LIMITS for v in (math.nextafter(limit, 0.0), limit, math.nextafter(limit, 1.0))),
})
RHOS = sorted({s * r for r in RHOS for s in (1.0, -1.0)})
# Thresholds the quadrature meets in turn: the origin, both signs and both
# orderings, the near and far tails, equal and opposite arguments, a saturated
# corner, and the -3/-3, -6/-6 and -20/1 cancellation corners of MorphIQ Risk's
# bivariate-normal audit (#380).
PAIRS = [(0.0, 0.0), (0.25, -0.25), (1.0, 1.0), (-1.0, -1.0), (1.0, -2.0), (2.0, 3.5),
         (-2.0, -3.5), (3.5, -3.5), (-3.0, -3.0), (-3.0, 3.0), (-6.0, -6.0), (-6.0, -9.0),
         (6.0, 9.0), (-9.0, 15.0), (15.0, -26.0), (-26.0, -37.5), (-37.5, -38.5), (0.0, -9.0),
         (0.0, 9.0), (-20.0, 1.0), (37.5, 38.5)]


# The deep-tail negative-correlation corner of MorphIQ Risk's issue #380: both
# arguments well below zero, correlation negative, where the direct Genz sum
# cancels to the rounding floor (about 1e16) and the reflection identity to
# 2e18. They are required cases, not samples.
HARD = [(-3.0, -3.0, -0.7861513777574233), (-6.0, -6.0, -0.9), (-20.0, 1.0, -0.5),
        (-3.0, -3.0, 0.7861513777574233), (-38.0, -30.0, 0.7861513777574233),
        (-8.0, -8.0, -0.5), (-12.0, -12.0, -0.95), (-5.0, -7.0, -0.99)]
# The high-correlation peak, where the 20-node rule's truncation is largest:
# |rho| just above the Genz split, one threshold near zero (docs/bivariate_normal_high.md).
PEAK = [(h, k, rho)
        for rho in (0.925, 0.9250000000000002, 0.93, 0.94, 0.954, 0.9755, 0.995, -0.925, -0.94, -0.9755)
        for h, k in ((-0.21101192279835226, -0.0014549743776884816),
                     (-0.0014549743776884816, -0.21101192279835226),
                     (-0.2, -0.001), (-0.38, 0.0), (0.21101192279835226, 0.0014549743776884816))]
# Probabilities of 1e-5 to 1e-25 in the lower tails, where the relative accuracy of a
# result follows the node count of the rule (docs/bivariate_normal.md section 4):
# the cases on which a rule shorter than the canonical Genz implementation's loses
# by orders of magnitude. The correlations straddle each rule's band.
TAIL = [(h, k, rho)
        for rho in (0.01, 0.05, 0.1, 0.25, 0.3, 0.45, 0.5, 0.6, 0.7, 0.78, 0.85, 0.9,
                    -0.05, -0.3, -0.5, -0.78, -0.85)
        for h, k in ((-4.0, -4.0), (-6.0, -6.0), (-8.0, -8.0), (-8.0, 3.0), (-10.0, 2.0),
                     (-9.0, -4.0), (-12.0, 0.0))]
# Lower tails at high correlation with hk = h k from 100 to 1400, where the
# correlation integral is most of the result and is computed out to the
# cutoff (docs/bivariate_normal_high.md section 1.7): probabilities from 1e-26
# to 1e-290.
DEEP = [(h, k, rho)
        for rho in (0.93, 0.95, 0.97, 0.99, 0.999, 0.99999, 1.0 - 2.0 ** -30)
        for h, k in ((-10.5, -10.5), (-12.0, -12.0), (-14.0, -14.0), (-17.0, -17.0),
                     (-20.0, -20.0), (-25.0, -25.0), (-30.0, -30.0), (-36.0, -36.0),
                     (-10.0, -30.0), (-20.0, -9.0), (-37.0, -37.83783783783783),
                     (-37.0, -37.83783783783784))]
MORPHIQ_RISK = ROOT / 'generators/bivariate_normal_morphiq_risk_inputs.json'


def phi(x):
    return mp.ncdf(x)


def theta_integral(h, k, upper, parts=64):
    """int_{-pi/2}^{upper} exp(-(h^2+k^2-2hk sin t) / (2 cos^2 t)) dt, tanh-sinh.

    Written in u = t + pi/2, where sin t = -cos u and cos^2 t = sin^2 u, the
    exponent is ((h + k)^2 - 4 h k sin^2(u/2)) / (2 sin^2 u): finite as u -> 0
    even when h + k = 0, where the textbook form subtracts two quantities of
    order 1 / u^2 and an endpoint node loses every digit. `upper` is asin(rho);
    the length of the u interval is acos(-rho), which keeps its relative
    accuracy as rho -> -1.
    """
    length = mp.acos(-mp.sin(upper))
    hk = h * k
    s = h + k

    def exponent(u):
        sh = mp.sin(u / 2)
        return (s * s - 4 * hk * sh * sh) / (2 * mp.sin(u) ** 2)

    # The integrand spans hundreds of orders of magnitude, and an adaptive
    # rule judges convergence against the magnitude it has seen: factor out the
    # smallest exponent on a fine grid and the ends, so the integrand handed to
    # the rule has a maximum of about one and its absolute error is a relative
    # one for the integral.
    grid = [length * (mp.mpf(i) + mp.mpf(1) / 2) / 400 for i in range(400)]
    values = [exponent(u) for u in grid] + [exponent(length)]
    best = min(range(400), key=lambda i: values[i])
    floor = min(values)
    centre, cell = grid[best], length / 400

    def f(u):
        if u == 0:
            return mp.mpf(0)
        return mp.exp(floor - exponent(u))

    points = {mp.mpf(0), length}
    points.update(length * mp.mpf(i) / parts for i in range(parts + 1))
    for e in range(3, 60, 4):
        points.add(length * mp.mpf(2) ** -e)
        points.add(length - length * mp.mpf(2) ** -e)
    for m in (0.25, 0.5, 1, 2, 4, 8, 16, 32, 64):
        for sign in (-1, 1):
            q = centre + sign * m * cell
            if 0 < q < length:
                points.add(q)
    points = sorted(points)
    scaled, error = mp.quad(f, points, error=True, maxdegree=10)
    assert error <= mp.mpf(10) ** (-mp.mp.dps // 2) * abs(scaled), (error, scaled)
    return mp.exp(-floor) * scaled


def p_lower(h, k, rho):
    """P(X <= h, Y <= k) when h + k <= 0, where P at rho = -1 is zero."""
    return theta_integral(h, k, mp.asin(rho)) / (2 * mp.pi)


def bvn(h, k, rho):
    h, k, rho = mp.mpf(h), mp.mpf(k), mp.mpf(rho)
    if rho == 1:
        return phi(min(h, k))
    if rho == -1:
        return max(mp.mpf(0), 1 - phi(-h) - phi(-k))
    if h + k <= 0:
        return p_lower(h, k, rho)
    return 1 - phi(-h) - phi(-k) + p_lower(-h, -k, rho)


def owen_t(h, a):
    """Owen's T(h, a) = 1/(2 pi) int_0^a exp(-h^2 (1 + x^2) / 2) / (1 + x^2) dx."""
    if a == 0:
        return mp.mpf(0)
    if a < 0:
        return -owen_t(h, -a)
    scale = 1 / max(abs(h), mp.mpf(1) / 1000)
    points = sorted({mp.mpf(0), a} | {c * scale for c in (0.25, 1, 4, 16, 64) if c * scale < a})
    return mp.quad(lambda x: mp.exp(-h * h * (1 + x * x) / 2) / (1 + x * x), points) / (2 * mp.pi)


def bvn_owen(h, k, rho):
    """Second route (hk != 0): Owen's decomposition by T functions.

    P = Phi(h)/2 + Phi(k)/2 - T(h, a_h) - T(k, a_k) - delta, which subtracts
    quantities of order one, so a result near 10^-d needs about d digits more
    than the working precision; the caller supplies them.
    """
    h, k, rho = mp.mpf(h), mp.mpf(k), mp.mpf(rho)
    s = mp.sqrt(1 - rho * rho)
    ah, ak = (k - rho * h) / (h * s), (h - rho * k) / (k * s)
    delta = 0 if h * k > 0 else mp.mpf(1) / 2
    return phi(h) / 2 + phi(k) / 2 - owen_t(h, ah) - owen_t(k, ak) - delta


def bvn_plackett(h, k, rho):
    """Third route (0 < rho < 1): Plackett's identity,

    P = Phi(h) Phi(k) + int_0^rho exp(-(h^2 - 2 r h k + k^2) / (2 (1 - r^2))) / (2 pi sqrt(1 - r^2)) dr.

    Its integrand is positive, so a result far below 1e-46 is held to its own
    relative size with no cancellation; r = 1 - e^t puts its peak, which sits
    within a distance of 1 comparable to 1 - rho, on a scale the quadrature resolves.
    """
    h, k, rho = mp.mpf(h), mp.mpf(k), mp.mpf(rho)
    assert 0 < rho < 1

    def f(r):
        return mp.exp(-(h * h - 2 * r * h * k + k * k) / (2 * (1 - r * r))) / (2 * mp.pi * mp.sqrt(1 - r * r))

    a, n = mp.log(1 - rho), 1500
    points = [a - a * mp.mpf(i) / n for i in range(n + 1)]
    integral = mp.quad(lambda t: f(1 - mp.exp(t)) * mp.exp(t), points, method='gauss-legendre', maxdegree=7)
    return phi(h) * phi(k) + integral


def at(precision, function, *args):
    with mp.workdps(int(precision * 0.30103) + 5):
        return function(*args)


def text(value):
    return mp.nstr(value, DIGITS, strip_zeros=False) if value != 0 else '0'


def cases():
    out = []
    rng = splitmix64(0x38B1_7A21_D00D_F00D)
    for rho in RHOS:
        for h, k in PAIRS:
            out.append((h, k, rho, 'grid', None))
    for h, k, rho in HARD:
        out.append((h, k, rho, 'hard', None))
    for h, k, rho in PEAK:
        out.append((h, k, rho, 'peak', None))
    for _ in range(200):
        h = (next(rng) / 2.0 ** 64 * 2 - 1) * 12
        k = (next(rng) / 2.0 ** 64 * 2 - 1) * 12
        rho = (next(rng) / 2.0 ** 64 * 2 - 1)
        out.append((h, k, rho, 'random', None))
    for row in json.loads(MORPHIQ_RISK.read_text())['rows']:
        h, k, rho = (from_bits(int(row[name], 16)) for name in ('h', 'k', 'rho'))
        out.append((h, k, rho, 'morphiq_risk', (row['family'], row['status'], row['value'])))
    for h, k, rho in TAIL:
        out.append((h, k, rho, 'tail', None))
    for h, k, rho in DEEP:
        out.append((h, k, rho, 'deep', None))
    return out


def beyond_binary64(h, k, rho):
    """True when the probability is rigorously below 1e-330, so its binary64 value is 0.

    For h, k < 0 and rho < 0 the quadrant lies in the half-plane tangent at its
    corner (moving into the quadrant raises the quadratic form), so
    P <= Phi(-d) <= exp(-d^2 / 2) / 2 with d^2 = (h^2 + k^2 - 2 rho h k) / (1 - rho^2).
    Their exact evaluation costs hours and says nothing more than 0.
    """
    if not (h < 0 and k < 0 and rho < 0):
        return False
    with mp.workdps(40):
        h, k, rho = mp.mpf(h), mp.mpf(k), mp.mpf(rho)
        d2 = (h * h + k * k - 2 * rho * h * k) / (1 - rho * rho)
        return mp.exp(-d2 / 2) / 2 < mp.mpf(10) ** -330


def second_route(index, h, k, rho, kind):
    """Whether a second route (Owen's, or Plackett's for the deep cases) also evaluates the case."""
    if beyond_binary64(h, k, rho):
        return False
    if kind == 'deep':
        return 0 < rho < 1
    return h * k != 0 and abs(rho) <= 0.99 and index % 3 == 0


def evaluate(case):
    """One case at both precisions, plus the second route on a subset."""
    index, (h, k, rho, kind, morphiq_risk) = case
    if beyond_binary64(h, k, rho):
        row = {'kind': kind, 'h': f'{to_bits(h):016x}', 'k': f'{to_bits(k):016x}',
               'rho': f'{to_bits(rho):016x}', 'value': '0'}
        if morphiq_risk is not None:
            row['morphiq_risk'] = {'family': morphiq_risk[0], 'status': morphiq_risk[1], 'value': morphiq_risk[2]}
        return row, False, None
    lo, hi = (at(p, bvn, h, k, rho) for p in PRECISIONS)
    tolerance = max(abs(hi) * mp.mpf(10) ** -36, mp.mpf(10) ** -46)
    if kind == 'deep':
        # A value far below 1e-46 is held to its own relative size.
        tolerance = abs(hi) * mp.mpf(10) ** -30
    assert abs(lo - hi) <= tolerance, (h, k, rho, lo, hi)
    crossed = False
    if kind == 'deep' and second_route(index, h, k, rho, kind):
        # Plackett's identity at working precision 170 bits: the value is held
        # to 1e-28 relative to a route that shares no integral with the first.
        other = at(170, bvn_plackett, h, k, rho)
        assert abs(other - hi) <= abs(hi) * mp.mpf(10) ** -28, (h, k, rho, other, hi)
        crossed = True
    elif second_route(index, h, k, rho, kind):
        # Owen's route needs the digits the value lacks: its subtractions
        # cancel to the size of the result.
        depth = 0 if hi == 0 else max(0, int(-mp.log10(abs(hi))))
        other = at(300 + int(3.33 * depth), bvn_owen, h, k, rho)
        assert abs(other - hi) <= max(abs(hi) * mp.mpf(10) ** -30, mp.mpf(10) ** -50), \
            (h, k, rho, other, hi)
        crossed = True
    row = {
        'kind': kind,
        'h': f'{to_bits(h):016x}', 'k': f'{to_bits(k):016x}', 'rho': f'{to_bits(rho):016x}',
        'value': text(hi),
    }
    disagreement = None
    if morphiq_risk is not None:
        family, status, value = morphiq_risk
        row['morphiq_risk'] = {'family': family, 'status': status, 'value': value}
        # The earlier fixture prints 15 significant digits: where it called a
        # row resolved ours must agree to the rounding of those digits.
        if status == 'resolved' and abs(mp.mpf(value) - hi) > mp.mpf('6e-15') * abs(hi):
            disagreement = (family, row['h'], row['k'], row['rho'], value, text(hi))
    return row, crossed, disagreement


def evaluate_indexed(case):
    started = time.monotonic()
    result = evaluate(case)
    elapsed = time.monotonic() - started
    if elapsed > 30:
        print(f'bivariate_normal: case {case[0]} took {elapsed:.0f}s', file=sys.stderr, flush=True)
    return case[0], result


def generate(shard=None):
    """Every case, or only those whose index is congruent to `shard[0]` modulo `shard[1]`."""
    work = list(enumerate(cases()))
    if shard is not None:
        work = [item for item in work if item[0] % shard[1] == shard[0]]
    results = []
    with Pool(int(os.environ.get('BVN_WORKERS', '3'))) as pool:
        for done, result in enumerate(pool.imap_unordered(evaluate_indexed, work, chunksize=4), 1):
            results.append(result)
            if done % 100 == 0 or done == len(work):
                print(f'bivariate_normal: {done}/{len(work)} cases', file=sys.stderr, flush=True)
    results = [result for _, result in sorted(results, key=lambda pair: pair[0])]
    rows = [row for row, _, _ in results]
    cross = sum(1 for _, crossed, _ in results if crossed)
    disagreements = [d for _, _, d in results if d is not None]
    assert not disagreements, disagreements[:5]
    if shard is None:
        assert cross >= 300, cross
    return {'generator': 'generators/bivariate_normal_reference.py', 'mpmath': mp.__version__,
            'precision_bits': list(PRECISIONS), 'digits': DIGITS, 'cross_checked': cross,
            'morphiq_risk_disagreements': disagreements, 'cases': rows}


def check_shard(index, count):
    """Replays the cases of one shard against the committed fixture.

    The whole replay costs hours of CPU, so CI splits it over `count` jobs; the
    shards partition the case indices, so together they replay every row. Each
    shard also holds the header and the cross-checked total, which need no
    evaluation, to the committed file.
    """
    committed = json.loads(OUT.read_text())
    every = list(enumerate(cases()))
    if len(committed['cases']) != len(every):
        sys.exit(f'{OUT} holds {len(committed["cases"])} cases, the generator defines {len(every)}')
    total = sum(1 for i, (h, k, rho, kind, _) in every if second_route(i, h, k, rho, kind))
    fresh = generate((index, count))
    if committed['cross_checked'] != total or committed['morphiq_risk_disagreements']:
        sys.exit(f'{OUT} header differs: cross_checked {committed["cross_checked"]} vs {total}')
    for name in ('generator', 'mpmath', 'precision_bits', 'digits'):
        if committed[name] != fresh[name]:
            sys.exit(f'{OUT} {name} differs from a fresh generation')
    mine = [i for i, _ in every if i % count == index]
    for i, row in zip(mine, fresh['cases']):
        if committed['cases'][i] != row:
            sys.exit(f'{OUT} case {i} differs from a fresh generation')
    print(f'bivariate_normal: shard {index}/{count}: {len(mine)} cases replayed')


def main():
    args = sys.argv[1:]
    if '--shard' in args:
        index, count = (int(x) for x in args[args.index('--shard') + 1].split('/'))
        assert 0 <= index < count
        check_shard(index, count)
        return
    result = generate()
    out = json.dumps(result, indent=1) + '\n'
    if '--check' in args:
        if OUT.read_text() != out:
            sys.exit(f'{OUT} differs from a fresh generation')
    else:
        OUT.write_text(out)
    print(f'bivariate_normal: {len(result["cases"])} cases, {result["cross_checked"]} cross-checked, '
          f'{len(result["morphiq_risk_disagreements"])} disagreements with the MorphIQ Risk rows')


if __name__ == '__main__':
    main()
