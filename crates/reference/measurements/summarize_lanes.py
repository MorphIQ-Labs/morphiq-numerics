#!/usr/bin/env python3
"""Summarize `native_performance` CSV runs (crates/morphiq-numerics/src/lanes/tests/bench.rs).

    python3 -I summarize_lanes.py OUT_DIR lanes-1.csv lanes-2.csv ...

Pools every timed round of every run. Writes OUT_DIR/summary.csv (time
records: median, min and max ns per element, median ns per call, and the
scalar loop's median at the same length over the mode's), OUT_DIR/cache.csv
and OUT_DIR/paths.csv. Path and table records must agree across runs: the
workloads are fixed-seed, so a difference means the runs measured different
code. Standard library only; no timing threshold is applied.
"""

import csv
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def records(path):
    with open(path, newline="") as f:
        for row in csv.reader(f):
            if row and row[0] in {"time", "path", "table", "cache", "backends"}:
                yield row


def main():
    out = Path(sys.argv[1])
    runs = sys.argv[2:]
    if not runs:
        sys.exit(__doc__)
    times = defaultdict(list)
    calls = defaultdict(list)
    cache = defaultdict(list)
    fixed = None
    for run in runs:
        static = []
        for row in records(run):
            kind = row[0]
            if kind == "time":
                _, function, workload, length, mode, _round, ns, per_call = row
                key = (function, workload, int(length), mode)
                times[key].append(float(ns))
                calls[key].append(float(per_call))
            elif kind == "cache":
                _, function, working_set, mode, _round, ns = row
                cache[(function, int(working_set), mode)].append(float(ns))
            else:
                static.append(row)
        if fixed is None:
            fixed = static
        elif static != fixed:
            sys.exit(f"{run}: path, table or backend records differ from {runs[0]}")
    out.mkdir(parents=True, exist_ok=True)
    with open(out / "summary.csv", "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["function", "workload", "length", "mode", "samples",
                    "ns_per_element_median", "ns_per_element_min", "ns_per_element_max",
                    "ns_per_call_median", "speedup_over_scalar"])
        for key in sorted(times):
            function, workload, length, mode = key
            v = times[key]
            median = statistics.median(v)
            scalar = times.get((function, workload, length, "scalar"))
            speedup = (f"{statistics.median(scalar) / median:.3f}"
                       if scalar and not mode.startswith("chain") else "")
            w.writerow([function, workload, length, mode, len(v), f"{median:.3f}",
                        f"{min(v):.3f}", f"{max(v):.3f}",
                        f"{statistics.median(calls[key]):.3f}", speedup])
    with open(out / "cache.csv", "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["function", "working_set_bytes", "mode", "samples",
                    "ns_per_element_median", "ns_per_element_min", "ns_per_element_max"])
        for key in sorted(cache):
            v = cache[key]
            w.writerow([*key, len(v), f"{statistics.median(v):.3f}",
                        f"{min(v):.3f}", f"{max(v):.3f}"])
    with open(out / "paths.csv", "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        for row in fixed:
            w.writerow(row)


if __name__ == "__main__":
    main()
