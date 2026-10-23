#!/usr/bin/env python3
"""Summarize retained ABBA samples under issue #219's declared protocol.

Usage: summarize_tridiagonal_bench.py raw.csv > summary.json
No samples are silently discarded. Intervals are the order-statistic interval
for the median of 21 independent paired ratios (coverage 97.34%); host drift
or serial dependence can invalidate that independence assumption.
"""
import csv
import json
from math import comb
import statistics as stats
import sys

groups = {}
with open(sys.argv[1]) as source:
    for row in csv.DictReader(source):
        key = tuple(row[x] for x in ('kind', 'n', 'rhs', 'pair'))
        groups.setdefault(key, []).append(row)

result = []
for (kind, n, rhs, pair), rows in groups.items():
    methods = pair.split(':')
    samples = {method: [] for method in methods}
    ratios = []
    rounds = {}
    for row in rows:
        rounds.setdefault(int(row['round']), {}).setdefault(row['method'], []).append(
            int(row['elapsed_ns']) / int(row['calls']))
    assert len(rounds) == 21
    for round_samples in rounds.values():
        assert all(len(round_samples[method]) == 2 for method in methods)
        means = [stats.mean(round_samples[method]) for method in methods]
        ratios.append(means[0] / means[1])
        for method in methods:
            samples[method].extend(round_samples[method])
    record = dict(kind=kind, n=int(n), rhs=int(rhs), pair=pair, methods={})
    unstable = False
    for method, values in samples.items():
        q1, _, q3 = stats.quantiles(values, n=4, method='inclusive')
        median = stats.median(values)
        relative_iqr = (q3-q1)/median
        drift = stats.median(values[-10:])/stats.median(values[:10])-1
        record['methods'][method] = dict(median_ns=median, q1_ns=q1, q3_ns=q3,
                                         relative_iqr=relative_iqr, last_first_drift=drift)
        unstable |= relative_iqr > 0.10
        if method == 'copy_control':
            unstable |= abs(drift) > 0.05
    ordered = sorted(ratios)
    record.update(ratio_median=stats.median(ratios), ratio_interval=[ordered[5], ordered[15]],
                  interval_coverage=1-2*sum(comb(21, k) for k in range(6))/2**21,
                  unstable=unstable)
    result.append(record)
json.dump(result, sys.stdout, indent=2)
print()
