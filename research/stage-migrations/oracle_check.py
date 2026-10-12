#!/usr/bin/env python3
"""Check a research harness JSONL export against independent interval arithmetic.

Uses generators/oracle (mpmath pinned by generators/requirements.txt), requiring
both interval endpoints to round alike at two successive precisions. Expected
results never come from the baseline or the experimental implementation.
Run with target/generators-venv/bin/python from the repository root.
"""
import collections
import json
import math
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'generators'))
from oracle import correctly_rounded, from_bits, to_bits  # noqa: E402
from mpmath import iv  # noqa: E402
import mpmath  # noqa: E402


def reference(name, x):
    if math.isnan(x):
        return math.nan
    if name == 'ln':
        if x == 0:
            return -math.inf
        if x < 0:
            return math.nan
        if x == math.inf:
            return math.inf
        return correctly_rounded(iv.ln, x)
    if name == 'exp2':
        # Exact binary thresholds: 2^1024 overflows; 2^-1075 is the tie to zero.
        if x >= 1024:
            return math.inf
        if x <= -1075:
            return 0.0
        return correctly_rounded(lambda v: iv.exp(v * iv.ln(2)), x)
    assert name == 'expm1'
    if x == 0:
        return x
    # Far outside either transition, e > 2 suffices to establish saturation.
    if x >= 1024:
        return math.inf
    if x <= -2048:
        return -1.0
    # exp(x)-1 in the oracle needs enough precision to retain tiny x before
    # subtraction. The prototype's small path is not used to set its answer.
    start = max(128, 128 - math.frexp(abs(x))[1])
    return correctly_rounded(lambda v: iv.exp(v) - 1, x, start=start)


def main():
    if mpmath.__version__ != '1.4.1':
        sys.exit('Use generators/requirements.txt: mpmath 1.4.1 is required')
    counts = collections.Counter()
    with pathlib.Path(sys.argv[1]).open() as source:
        for line in source:
            row = json.loads(line)
            x = from_bits(int(row['x'], 16))
            actual = from_bits(int(row['actual'], 16))
            expected = reference(row['function'], x)
            if not (math.isnan(actual) and math.isnan(expected)):
                assert to_bits(actual) == to_bits(expected), (row, f'{to_bits(expected):016x}')
            counts[row['function']] += 1
    print('Independent mpmath 1.4.1 interval checks passed:', dict(counts))


if __name__ == '__main__':
    main()
