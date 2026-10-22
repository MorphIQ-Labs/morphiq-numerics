#!/usr/bin/env python3
"""Independent interval oracles for docs/log_normalize.md.

Uses mpmath interval exponentials/logarithms on exact binary64 inputs, never
the implementation's compensated floating-point reduction. Inward-rounded
acceptance endpoints enforce the derived mathematical error, not a sampled
tolerance. Outward-rounded truth endpoints separately check returned radii.
The enclosing arithmetic and underflow enclosure are shared with the audited
log-sum reference generator. Precision doubles until every enclosure is at
least 40 bits narrower than the allowed error. Uniform cases also use the
independent closed form -log(n). Requires pinned generators/requirements.txt.
"""
import json
import math
import pathlib
import sys
from fractions import Fraction as F

from mpmath import iv
from log_space_bounds import CLAIM_NORMALIZE_REL, TINY, U, CLAIM_LSE_N_MAX
from log_space_reference import lse_enclosure, ends, abs_min, rd, ru, hex64
from oracle import splitmix64

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/log_normalize.json'


def case(xs, label):
    finite = [x for x in xs if math.isfinite(x)]
    m = max(finite)
    precision = 256
    while True:
        iv.prec = precision
        _, correction = lse_enclosure(finite)
        truths = []
        accepted = []
        narrow = True
        for x in xs:
            if x == -math.inf:
                truths.append((-math.inf, -math.inf))
                accepted.append((-math.inf, -math.inf))
                continue
            # The exact-real normalized logarithm. Fraction removes any
            # binary64 common-offset subtraction from the oracle.
            delta = F(x) - F(m)
            d = iv.mpf(delta.numerator) / delta.denominator
            lo, hi = ends(d - correction)
            bound = CLAIM_NORMALIZE_REL * U * abs_min(lo, hi) + 2 * len(finite) * TINY
            narrow &= hi - lo <= bound / 2**40
            accepted.append((ru(hi - bound), rd(lo + bound)))
            # Halving is exact for the large outputs here and keeps an
            # outward truth endpoint finite when the real value lies just
            # below -MAX but still rounds to finite binary64. Small outputs
            # use the same scale with the subnormal allowance below.
            truths.append((rd(lo / 2), ru(hi / 2)))
            if len(set(finite)) == 1:
                exact = -iv.log(len(finite))
                a, b = ends(exact)
                assert max(a, lo) <= min(b, hi), 'uniform closed forms disagree'
        if narrow:
            break
        precision *= 2
        if precision > 65536:
            raise RuntimeError(f'{label}: failed to resolve interval oracle')
    assert all(lo <= hi for lo, hi in accepted), label
    return dict(label=label, x=' '.join(map(hex64, xs)),
                lo=' '.join(hex64(a) for a, _ in accepted),
                hi=' '.join(hex64(b) for _, b in accepted),
                truth_lo=' '.join(hex64(a) for a, _ in truths),
                truth_hi=' '.join(hex64(b) for _, b in truths))


def cases():
    yield case([0., 0.], 'uniform-two')
    yield case([0., 0., 0.], 'uniform-three')
    yield case([float.fromhex('0x1p1000')] * 3, 'huge-positive-common-offset')
    yield case([-float.fromhex('0x1p1000')] * 3, 'huge-negative-common-offset')
    yield case([0., -800., -math.inf, -1600.], 'finite-mass-below-ordinary-underflow')
    yield case([0., -744., -745., -746., -740.], 'subnormal-exponential-tails')
    yield case([0., math.nextafter(0., -math.inf), -math.inf], 'subnormal-shift')
    yield case([math.nextafter(0., math.inf), 0., math.nextafter(0., -math.inf)], 'opposite-subnormal-inputs')
    maximum = float.fromhex('0x1.fffffffffffffp1023')
    yield case([maximum, math.nextafter(maximum, 0.), maximum], 'maximum-offset-ties')
    yield case([-maximum, -math.nextafter(maximum, 0.), -maximum], 'minimum-offset-ties')
    yield case([0., -maximum, -math.inf], 'representable-maximum-log-span')
    yield case([-32.125, -32.12500000000001, -40., -65.], 'irregular-compensated-tail')
    yield case([0., -50., -60.], 'dominant-log-smaller-than-epsilon')
    words = splitmix64(0x6c6f675f6e6f726d)
    for n in [2, 3, 4, 7, 8, 31, 32, 33, 63, 64, 65, 127, 128, 257, 1025]:
        xs = []
        for _ in range(n):
            word = next(words)
            xs.append((word >> 11) * 2.0**-53 * 100 - 50)
        yield case(xs, f'irregular-{n}')
        yield case([v if i % 3 else -math.inf for i, v in enumerate(xs)], f'zeros-{n}')
        yield case([0.] + [-740. - (i % 17) for i in range(n - 1)], f'tails-{n}')


def main():
    rows = list(cases())
    # At the maximum qualified count, a closed-form compact fixture avoids
    # committing millions of duplicate inputs and outputs.
    iv.prec = 256
    lo, hi = ends(-iv.log(CLAIM_LSE_N_MAX))
    b = CLAIM_NORMALIZE_REL * U * abs_min(lo, hi) + 2 * CLAIM_LSE_N_MAX * TINY
    uniform = dict(count=str(CLAIM_LSE_N_MAX), lo=hex64(ru(hi - b)), hi=hex64(rd(lo + b)))
    result = json.dumps(dict(cases=rows, maximum_uniform=[uniform]), indent=2) + '\n'
    if '--check' in sys.argv:
        if not OUTPUT.exists() or OUTPUT.read_text() != result:
            raise SystemExit('log normalization reference differs from fresh generation')
    else:
        OUTPUT.write_text(result)
    print(f'log normalization: {len(rows)} interval cases and maximum-count closed form checked')


if __name__ == '__main__':
    main()
