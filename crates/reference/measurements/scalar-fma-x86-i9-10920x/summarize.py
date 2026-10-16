#!/usr/bin/env python3
"""Summarize paired benchmark CSVs: OUT_DIR RUN.csv [RUN.csv ...]."""
import csv
import statistics
import sys
from collections import defaultdict
from pathlib import Path

out = Path(sys.argv[1])
times = defaultdict(list)
keys = None
for name in sys.argv[2:]:
    with open(name, newline="") as stream:
        reader = csv.DictReader(stream)
        columns = [k for k in reader.fieldnames if k not in {"round", "variant", "ns"}]
        if keys is None:
            keys = columns
        if columns != keys:
            raise ValueError(f"{name}: different workload columns")
        for row in reader:
            times[(*[row[k] for k in keys], int(row["variant"]))].append(float(row["ns"]))
if not times:
    raise ValueError("no timing samples")
out.mkdir(parents=True, exist_ok=True)
with (out / "summary.csv").open("w", newline="") as stream:
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow([*keys, "variant", "samples", "median_ns", "min_ns", "max_ns"])
    for key, samples in sorted(times.items()):
        writer.writerow([*key, len(samples), *[f"{v:.5f}" for v in (statistics.median(samples), min(samples), max(samples))]])
with (out / "comparison.csv").open("w", newline="") as stream:
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow([*keys, "before_ns", "after_ns", "after_over_before"])
    for key in sorted({key[:-1] for key in times}):
        variants = sorted(k[-1] for k in times if k[:-1] == key)
        before = statistics.median(times[(*key, variants[0])])
        after = statistics.median(times[(*key, variants[-1])])
        writer.writerow([*key, f"{before:.5f}", f"{after:.5f}", f"{after/before:.5f}"])
