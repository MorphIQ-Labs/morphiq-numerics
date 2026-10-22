#!/usr/bin/env python3
"""Paired native LAPACK diagnostic timings; build instructions in issue #219.

Usage: bench_tridiagonal_lapack.py RUST_BINARY LAPACK_BINARY CPU > raw.csv
Reference LAPACK 3.12.1 is a different-contract comparator. Factor timings
include copying immutable input coefficients; solve timings include RHS copy.
No process-launch or fixture setup time is inside a returned elapsed interval.
"""
import csv
import os
from pathlib import Path
import subprocess
import sys

rust, lapack, cpu = sys.argv[1:]
env = dict(os.environ)
env['LD_LIBRARY_PATH'] = str(Path(lapack).resolve().parent / 'native-libs')
writer = csv.writer(sys.stdout)
writer.writerow(['kind', 'n', 'rhs', 'pair', 'method', 'round', 'position', 'calls', 'elapsed_ns'])


def run(method, n, kind, rhs, calls):
    if method.startswith('lapack_'):
        args = [lapack, str(n), kind, method.removeprefix('lapack_'), 'fortran', str(calls), str(rhs)]
    else:
        args = [rust, '--one', str(n), kind, method, str(calls), str(rhs)]
    return int(subprocess.check_output(['taskset', '-c', cpu, *args], env=env))


for n in [1, 3, 17, 401, 4096]:
    for kind in ['ordinary', 'mixed', 'near']:
        for a, b, rhs in [('factor', 'lapack_factor', 1), ('solve', 'lapack_solve', 1),
                          *[('reused', 'lapack_group', k) for k in [1, 8, 64]]]:
            counts = {method: max(1, 160_000_000 // max(1, run(method, n, kind, rhs, 16)))
                      for method in [a, b]}
            for method in [a, b, b, a]:
                run(method, n, kind, rhs, counts[method])
            for round_number in range(21):
                for position, method in enumerate([a, b, b, a]):
                    elapsed = run(method, n, kind, rhs, counts[method])
                    writer.writerow([kind, n, rhs, a+':'+b, method, round_number, position, counts[method], elapsed])
                sys.stdout.flush()
