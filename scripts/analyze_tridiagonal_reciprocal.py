#!/usr/bin/env python3
"""Exact, independent error diagnostics for the reciprocal experiment outputs.

Usage: analyze_tridiagonal_reciprocal.py NUMERICAL_JSON FIXTURE_JSON
Reported errors describe these fixtures only; no uniform error budget is inferred.
"""
from fractions import Fraction
import json
import struct
import sys


def exact(bits):
    return Fraction.from_float(struct.unpack('>d', bytes.fromhex(bits))[0])


results = json.load(open(sys.argv[1]))
fixtures = {x['name']: x for x in json.load(open(sys.argv[2]))['cases']}
for row in results:
    reference = [Fraction(int(n), int(d)) for n, d in fixtures[row['case']]['solution']]
    errors = {}
    for method in ['baseline', 'candidate']:
        values = [exact(bits) for bits in row[method+'_bits']]
        assert len(values) == len(reference)
        error = max((abs(x-y) for x, y in zip(values, reference)), default=Fraction(0))
        bound = Fraction.from_float(row[method+'_solution_bound'])
        assert error <= bound
        row[method+'_max_exact_error'] = str(error)
        row[method+'_max_error_approx'] = float(error)
        errors[method] = error
    row['error_comparison'] = ('larger' if errors['candidate'] > errors['baseline'] else
                               'smaller' if errors['candidate'] < errors['baseline'] else 'equal')
json.dump(results, sys.stdout, indent=2)
print()
