#!/usr/bin/env python3
"""Exact rational variance oracle for the benchmark's recorded binary64 inputs."""
import csv
from fractions import Fraction
import itertools
import json
from pathlib import Path
import struct
import sys


def number(bits):
    return struct.unpack('>d', bytes.fromhex(bits))[0]


def check(path):
    inputs, outputs = {}, {}
    names = ('moments', 'checked_welford', 'ordinary_welford', 'corrected_two_pass')
    for row in csv.reader(Path(path).read_text().splitlines()):
        if not row or row[0] not in {'moment_input', 'moment_observation'}:
            continue
        if row[1] == 'region':
            continue
        _, region, n, *rest = row
        cell = (int(region), int(n))
        if row[0] == 'moment_input':
            index, bits = rest
            key = (*cell, int(index))
            if key in inputs:
                raise ValueError('duplicate input')
            inputs[key] = Fraction.from_float(number(bits))
        else:
            name, value, error = rest
            key = (*cell, name)
            if key in outputs:
                raise ValueError('duplicate observation')
            outputs[key] = (number(value), number(error))
    cells = list(itertools.product(range(4), (3, 65, 4096)))
    if set(inputs) != {(*c, i) for c in cells for i in range(c[1])}:
        raise ValueError('missing/unknown input bits')
    if set(outputs) != {(*c, name) for c in cells for name in names}:
        raise ValueError('missing/unknown observations')
    results = []
    for cell in cells:
        n = cell[1]
        xs = [inputs[*cell, i] for i in range(n)]
        # Independent exact raw sums; cancellation is exact here.
        total = sum(xs)
        variance = (n * sum(x*x for x in xs) - total*total) / (n*(n-1))
        for name in names:
            value, bound = outputs[*cell, name]
            error = abs(Fraction.from_float(value) - variance)
            certified = name in names[:2]
            if certified and not error <= Fraction.from_float(bound):
                raise AssertionError(f'false certificate: {cell} {name}')
            results.append({'cell': cell, 'name': name,
                            'absolute_error': float(error),
                            'relative_error': float(error / variance),
                            'reported_absolute_bound': bound if certified else None,
                            'reported_relative_bound': float(Fraction.from_float(bound) / variance) if certified else None})
    return results


if __name__ == '__main__':
    print(json.dumps(check(sys.argv[1]), indent=2, allow_nan=False))
