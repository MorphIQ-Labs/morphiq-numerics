#!/usr/bin/env python3
"""The heuristic estimate in docs/atan2.md section 6: how many binary64 pairs
(y, x) could lie within the accurate path's relative window of a rounding
midpoint. A HEURISTIC, not a proof: it assumes the bits of atan2 past the 54th are
equidistributed, which nothing here proves. Prints the figures the document
quotes. With --check, fails unless docs/atan2.md quotes exactly the figures printed here.
Needs mpmath (generators/requirements.txt) through atan2_certificates."""
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

# The accurate path's relative bound as the Coq proof establishes it for the transcription:
# `bndM = 5.2e-58` in formal/atan2/Atan2NewtonReal.v, used by Atan2Accurate.atan2_accurate_ok
# (the Gappa certificate newton.g claims a tighter 2^-190.6 under its own accounting; the
# estimate below uses the proved bound, the weaker of the two).
DELTA = 5.2e-58
LOG_DELTA = math.log2(DELTA)

# Midpoint distance of a quotient of 53-bit significands: at least 2^-107 relatively
# (docs/atan2.md section 3's argument; also not machine-checked).
RHO_LOG = -107.0
# Effective distinct angles per exponent difference e = exponent(d) - exponent(n):
# n and d are normal with 52 fraction bits each, 2^104 significand pairs per e (the
# absolute scale does not change the angle; y's sign only negates it). Upper bound:
# equal ratios are counted once per pair.
LOG_PAIRS_PER_E = 104.0
# Forms (docs/atan2.md section 3) and the largest e at which the window can contain a
# midpoint at all. Form phi = atan t: atan t differs from t by a relative t^2/3, and
# t is >= 2^-107 relatively from every midpoint, so beyond t^2/3 < 2^-107 - delta
# (t < 2^-52.7) nothing is within the window. Forms pi/2 -+ phi: pi/2 sits 0.28 ulp
# from RN(pi/2), so phi must reach 0.22 ulp (2^-54.2, t >= 2^-54.2) before a midpoint
# is in range; pi - phi: 0.22 ulp of pi, 2^-53.2.
FORMS = {'phi': 52, 'pi/2 - phi': 54, 'pi - phi': 53, 'pi/2 + phi': 54}
# Probability that a value equidistributed past bit 54 has a midpoint inside the
# two-sided relative window delta: 2 delta |Z| / ulp(Z), and E[|Z| / ulp(Z)] = 2^52 / ln 2
# for Z log-uniform within a binade (Benford).
LOG_P = 1 + LOG_DELTA + 52 + math.log2(1 / math.log(2))

total = sum(2.0 ** (LOG_PAIRS_PER_E) * (emax + 1) for emax in FORMS.values())
LOG_TOTAL = math.log2(total)
lines = [
    f'accurate bound delta = 2^{LOG_DELTA:.2f}',
    f'forms and deepest exponent difference: {FORMS}',
    f'effective pairs <= 2^{LOG_TOTAL:.2f} ({total:.3e})',
    f'per-pair probability 2^{LOG_P:.2f}',
    f'expected number of pairs inside a window 2^{LOG_TOTAL + LOG_P:.2f} ({total * 2.0 ** LOG_P:.2e})',
]
if '--check' in sys.argv[1:]:
    doc = (pathlib.Path(__file__).resolve().parent.parent / 'docs' / 'atan2.md').read_text()
    quoted = [f'2^{LOG_DELTA:.2f}', f'2^{LOG_TOTAL:.2f}', f'2^{LOG_P:.2f}',
              f'2^{LOG_TOTAL + LOG_P:.1f}', f'{total * 2.0 ** LOG_P:.1e}'.replace('e-0', '·10^-').replace('e-', '·10^-')]
    missing = [q for q in quoted if q not in doc]
    if missing:
        print(f'docs/atan2.md does not quote {missing}', file=sys.stderr)
        sys.exit(1)
else:
    print('\n'.join(lines))
