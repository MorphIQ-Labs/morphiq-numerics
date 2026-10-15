#!/usr/bin/env python3
"""Summarize the non-lanes outputs of run_native.sh in OUT_DIR.

    python3 -I summarize_native.py OUT_DIR

Pools every repetition (`*-N.*`) and writes, beside them, the median, minimum
and maximum of each measured value:

- normal-summary.csv: normal_local_performance, all workloads at 1,024 and
  `ordinary`/`mixed` at the short lengths (the length is the `count` column);
- consumer-summary.csv: the external-consumer benchmark (scalar and slice ns);
- log-space-summary.csv: log_space::tests::measure_cost;
- bench-batched-summary.csv, bench-exp-stages-summary.csv: their tables;
- bench-erfcx-summary.csv: bench-erfcx's rounds.

Standard library only; no timing threshold is applied.
"""

import csv
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def spread(values):
    return [f"{statistics.median(values):.3f}", f"{min(values):.3f}", f"{max(values):.3f}"]


def write(path, header, rows):
    with open(path, "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(header)
        w.writerows(rows)


def normal(out):
    values = defaultdict(lambda: defaultdict(list))
    accurate = {}
    for run in sorted(out.glob("normal-*.txt")):
        header = None
        for line in run.read_text().splitlines():
            line = line.split(" ... ", 1)[-1]
            if line.startswith("function,workload,count"):
                header = line.split(",")
                continue
            row = line.split(",")
            if header is None or len(row) != len(header):
                continue
            r = dict(zip(header, row))
            key = (r["function"], r["workload"], int(r["count"]))
            accurate[key] = r["accurate_count"]
            for column in ("scalar_ns", "batch_ns", "scalar_chain_ns", "chain_overhead_ns"):
                values[key][column].append(float(r[column]))
    rows = []
    for key in sorted(values):
        v = values[key]
        speedup = statistics.median(v["scalar_ns"]) / statistics.median(v["batch_ns"])
        rows.append([*key, accurate[key], len(v["scalar_ns"]), *spread(v["scalar_ns"]),
                     *spread(v["batch_ns"]), *spread(v["scalar_chain_ns"]),
                     *spread(v["chain_overhead_ns"]), f"{speedup:.3f}"])
    write(out / "normal-summary.csv",
          ["function", "workload", "count", "accurate_count", "samples",
           "scalar_ns_median", "scalar_ns_min", "scalar_ns_max",
           "batch_ns_median", "batch_ns_min", "batch_ns_max",
           "scalar_chain_ns_median", "scalar_chain_ns_min", "scalar_chain_ns_max",
           "chain_overhead_ns_median", "chain_overhead_ns_min", "chain_overhead_ns_max",
           "speedup"], rows)


def consumer(out):
    values = defaultdict(lambda: ([], []))
    for run in sorted(out.glob("consumer-*.txt")):
        for line in run.read_text().splitlines():
            name, scalar, batch = line.split(",")
            values[name][0].append(float(scalar))
            values[name][1].append(float(batch))
    write(out / "consumer-summary.csv",
          ["function", "samples", "scalar_ns_median", "scalar_ns_min", "scalar_ns_max",
           "batch_ns_median", "batch_ns_min", "batch_ns_max"],
          [[name, len(s), *spread(s), *spread(b)] for name, (s, b) in values.items()])


def log_space(out):
    values = defaultdict(list)
    for run in sorted(out.glob("log-space-*.txt")):
        for line in run.read_text().splitlines():
            m = re.search(r"([^.:]+(?:, [nN] = \d+)?): ([\d.]+) ns per (\w+)", line.split(" ... ", 1)[-1])
            if m:
                values[(m.group(1).strip(), m.group(3))].append(float(m.group(2)))
    write(out / "log-space-summary.csv",
          ["workload", "unit", "samples", "ns_median", "ns_min", "ns_max"],
          [[*key, len(v), *spread(v)] for key, v in values.items()])


def tables(out, stem):
    values = defaultdict(list)
    header = None
    for run in sorted(out.glob(f"{stem}-*.md")):
        for line in run.read_text().splitlines():
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if not line.startswith("|") or set(line) <= set("|-: "):
                continue
            if header is None:
                header = cells
            if cells == header:
                continue
            numeric = [i for i, c in enumerate(cells) if re.fullmatch(r"[\d.]+×?", c)]
            values[tuple(c for i, c in enumerate(cells) if i not in numeric)].append(
                [float(cells[i].rstrip("×")) for i in numeric])
    if header is None:
        return
    rows = []
    for key, runs in values.items():
        columns = list(zip(*runs))
        rows.append([*key, len(runs), *(f"{statistics.median(c):.3f}" for c in columns)])
    labels = [h for h in header if not re.search(r"\(ns\)|ns/|Speed", h)]
    numbers = [h for h in header if h not in labels]
    write(out / f"{stem}-summary.csv", [*labels, "runs", *(f"{h} (median)" for h in numbers)], rows)


def erfcx(out):
    values = defaultdict(list)
    for run in sorted(out.glob("bench-erfcx-*.csv")):
        with open(run, newline="") as f:
            for r in csv.DictReader(f):
                values[(r["range"], r["mode"])].append(float(r["ns_per_call"]))
    write(out / "bench-erfcx-summary.csv",
          ["range", "mode", "samples", "ns_median", "ns_min", "ns_max"],
          [[*key, len(v), *spread(v)] for key, v in values.items()])


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    out = Path(sys.argv[1])
    normal(out)
    consumer(out)
    log_space(out)
    tables(out, "bench-batched")
    tables(out, "bench-exp-stages")
    erfcx(out)


if __name__ == "__main__":
    main()
