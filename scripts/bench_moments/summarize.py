#!/usr/bin/env python3
"""Summarize one complete native moments attempt without trimming samples."""
import csv
import itertools
import json
import math
from pathlib import Path
import statistics
import sys


def summarize(path):
    names = {"moments", "checked_welford", "ordinary_welford", "corrected_two_pass"}
    samples = {}
    operations = {}
    for row in csv.reader(Path(path).read_text().splitlines()):
        if not row or row[0] not in {"moments", "moments_operation"}:
            continue
        if row[1] in {"region", "round"}:
            continue
        if row[0] == "moments":
            _, region, n, streams, round_, name, reps, ns = row
            key = (int(region), int(n), int(streams), int(round_), name)
            expected_reps = max(65536 // (int(n) * int(streams)), 8)
            destination = samples
        else:
            _, round_, operation, reps, ns = row
            key = (int(round_), int(operation))
            expected_reps = 65536
            destination = operations
        value = float(ns)
        if key in destination or not math.isfinite(value) or value <= 0:
            raise ValueError(f"duplicate or invalid measurement: {row}")
        if int(reps) != expected_reps:
            raise ValueError(f"unexpected repetition count: {row}")
        destination[key] = value
    expected = set(itertools.product(range(4), (3, 65, 4096), (1, 4), range(18), names))
    if set(samples) != expected:
        raise ValueError("missing or unknown comparison cells/rounds")
    if set(operations) != set(itertools.product(range(18), range(4))):
        raise ValueError("missing or unknown operation cells/rounds")
    result = []
    for region, n, streams in itertools.product(range(4), (3, 65, 4096), (1, 4)):
        cell = (region, n, streams)
        rows = {name: [samples[(*cell, r, name)] for r in range(3, 18)] for name in sorted(names)}
        ratios = [a / b for a, b in zip(rows["moments"], rows["checked_welford"])]
        wins = sum(r < 1 for r in ratios)
        median = statistics.median(ratios)
        result.append({"cell": cell, "primary": n != 3, "paired_ratios": ratios,
                       "median_ratio": median, "wins": wins,
                       "passed": median < 1 and wins >= 12,
                       "ns_per_observation": {
                           name: {"median": statistics.median(values),
                                  "quartiles": statistics.quantiles(values, n=4),
                                  "min": min(values), "max": max(values)}
                           for name, values in rows.items()}})
    return {"primary_passed": all(c["passed"] for c in result if c["primary"]),
            "cells": result, "operations_ns": {
                name: [operations[r, i] for r in range(3, 18)]
                for i, name in enumerate(("merge", "mean", "variance", "standard_error"))}}


if __name__ == "__main__":
    print(json.dumps(summarize(sys.argv[1]), indent=2))
