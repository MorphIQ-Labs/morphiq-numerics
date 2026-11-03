#!/usr/bin/env python3
"""Paired native qualification of the public normal-pair API on one host.

Uses the shared benchmark protocol, a prepared/observed screen directory,
and separate processes for each cell. This does not replace ARM measurements
or consumer end-to-end qualification. No compilation occurs during timing.
"""
import argparse
import ctypes as ct
import importlib.util
import json
import math
import os
from pathlib import Path
import statistics
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import screen

spec = importlib.util.spec_from_file_location("bench_protocol", HERE.parent / "protocol.py")
protocol = importlib.util.module_from_spec(spec)
spec.loader.exec_module(protocol)


def cells():
    result = []
    for reference in ["libm_direct", "libm_folded"]:
        for population in ["ordinary", "radial_edges", "octant_edges"]:
            result.append(dict(kind="scalar", population=population, n=4096, reference=reference))
        for population in ["ordinary", "radial_edges"]:
            result.append(dict(kind="latency", population=population, n=4096, reference=reference))
        for n in [1, 2, 7, 8, 9, 17, 4096]:
            result.append(dict(kind="slice", population="ordinary", n=n, reference=reference))
        for population in ["radial_edges", "octant_edges"]:
            result.append(dict(kind="slice", population=population, n=4096, reference=reference))
        for kind in ["stream", "antithetic"]:
            result.append(dict(kind=kind, population="xoshiro-seed-282", n=4096, reference=reference))
    for cell in result:
        cell["id"] = "{kind}-{population}-{n}-{reference}".format(**cell)
    return result


def host(cpu):
    def read(path):
        try:
            return Path(path).read_text().strip()
        except OSError:
            return None
    return dict(cpu=cpu, affinity=sorted(os.sched_getaffinity(0)), load=os.getloadavg(),
                governor=read(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor"),
                frequency_khz=read(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_cur_freq"),
                siblings=read(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list"),
                cpu_stat=read("/proc/stat"),
                thermal={str(p): read(p) for p in Path("/sys/class/thermal").glob("thermal_zone*/temp")})


def timers(prepared, cell):
    native, functions = screen.load(prepared)
    library = ct.CDLL(str(prepared / "target/release/libnormal_pair_screen.so"))
    native.measure.argtypes = [ct.c_void_p, ct.POINTER(ct.c_uint64), ct.POINTER(screen.Pair),
                              ct.c_size_t, ct.c_uint64]
    native.measure.restype = ct.c_uint64
    native.measure_chain.argtypes = native.measure.argtypes
    native.measure_chain.restype = ct.c_uint64
    library.measure_slice.argtypes = [ct.POINTER(ct.c_uint64), ct.POINTER(ct.c_uint64),
                                     ct.c_size_t, ct.c_uint64, ct.c_void_p]
    library.measure_slice.restype = ct.c_uint64
    library.measure_stream.argtypes = [ct.c_void_p, ct.c_uint64, ct.c_bool]
    library.measure_stream.restype = ct.c_uint64
    n = cell["n"]
    inputs = json.loads((prepared / "inputs.json").read_text())
    bank = inputs.get(cell["population"], inputs["ordinary"])[:n]
    words = (ct.c_uint64 * (2*n))(*(int(w, 16) for pair in bank for w in pair))
    first = (ct.c_uint64 * n)(*(int(pair[0], 16) for pair in bank))
    second = (ct.c_uint64 * n)(*(int(pair[1], 16) for pair in bank))
    out = (screen.Pair * n)()

    def elapsed(name, count):
        f = functions[name]
        if cell["kind"] in ["scalar", "latency"]:
            timer = native.measure if cell["kind"] == "scalar" else native.measure_chain
            return timer(f, words, out, n, count)
        if cell["kind"] == "slice":
            return library.measure_slice(first, second, n, count, None if name == "product" else f)
        return library.measure_stream(f, n*count, cell["kind"] == "antithetic")
    return elapsed


def worker(args):
    os.sched_setaffinity(0, {args.cpu})
    manifest = json.loads((args.out / "qualification-manifest.json").read_text())
    cell = next(c for c in manifest["cells"] if c["id"] == args.cell)
    measure = timers(args.prepared, cell)
    counts = manifest["counts"][args.cell]
    result = dict(cell=cell, process=args.worker, before=host(args.cpu), warmups=[], samples=[])
    for name in ["product", cell["reference"]]:
        count = max(1, counts[name] // 10)
        result["warmups"].append(dict(function=name, count=count, ns=measure(name, count)))
    for round_index in range(protocol.ROUNDS):
        order = ["product", cell["reference"]]
        if (args.worker + round_index) % 2:
            order.reverse()
        for name in order:
            ns = measure(name, counts[name])
            result["samples"].append(dict(function=name, round=round_index, ns=ns,
                                           count=counts[name], ns_per_pair=ns/(cell["n"]*counts[name])))
    result["after"] = host(args.cpu)
    path = args.out / f'{args.cell}-process-{args.worker}.json'
    with path.open("x") as f:
        json.dump(result, f, indent=2)
        f.write("\n")


def qualify(args):
    if not (args.prepared / "observations.json").exists():
        raise RuntimeError("Run the independent observations before qualification")
    screen.load(args.prepared)
    if screen.digest(Path(__file__)) != screen.digest(args.prepared / "templates/qualify.py"):
        raise RuntimeError("Qualification runner differs from the frozen preparation")
    if screen.digest(HERE.parent / "protocol.py") != screen.digest(args.prepared / "templates/protocol.py"):
        raise RuntimeError("Benchmark protocol differs from the frozen preparation")
    args.out.mkdir(parents=True, exist_ok=False)
    os.sched_setaffinity(0, {args.cpu})
    manifest = dict(cells=cells(), counts={}, before=host(args.cpu),
                    prepared=str(args.prepared), prepared_manifest_sha256=screen.digest(args.prepared / "manifest.json"),
                    runner_sha256=screen.digest(Path(__file__)),
                    protocol_sha256=screen.digest(HERE.parent / "protocol.py"),
                    processes=protocol.PROCESSES, rounds=protocol.ROUNDS,
                    target_ns=protocol.TARGET_NS, minimum_ns=protocol.MINIMUM_NS,
                    upper95_t9=protocol.T9_ONE_SIDED_95,
                    decision="Every cell must have upper one-sided 95% ratio <= 1 and every timed sample >= minimum_ns; no retries or outlier removal",
                    interpretation="One native x86-64-v3 Linux host; controlled CPU affinity, observed governor/frequency/thermal/contention. ARM and consumer qualification separate.")
    with (args.out / "calibration.jsonl").open("x", buffering=1) as log:
        for cell in manifest["cells"]:
            measure = timers(args.prepared, cell)
            counts = {}
            for name in ["product", cell["reference"]]:
                def record(kind, count, ns):
                    log.write(json.dumps(dict(cell=cell["id"], function=name, kind=kind,
                                              count=count, ns=ns)) + "\n")
                counts[name] = protocol.calibrate(lambda count: measure(name, count), record)
            manifest["counts"][cell["id"]] = counts
            print("Calibrated", cell["id"], flush=True)
    (args.out / "qualification-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    summaries = []
    for cell in manifest["cells"]:
        ratios, costs = [], {"product": [], cell["reference"]: []}
        valid = True
        for process in range(protocol.PROCESSES):
            subprocess.run([sys.executable, str(Path(__file__)), str(args.prepared),
                            "--out", str(args.out), "--cpu", str(args.cpu),
                            "--cell", cell["id"], "--worker", str(process)], check=True)
            sample = json.loads((args.out / f'{cell["id"]}-process-{process}.json').read_text())
            paired = []
            for round_index in range(protocol.ROUNDS):
                pair = {s["function"]: s for s in sample["samples"] if s["round"] == round_index}
                for name, row in pair.items():
                    valid &= row["ns"] >= protocol.MINIMUM_NS
                    costs[name].append(row["ns_per_pair"])
                paired.append(math.log(pair["product"]["ns_per_pair"] / pair[cell["reference"]]["ns_per_pair"]))
            ratios.append(statistics.mean(paired))
        upper = math.exp(statistics.mean(ratios) + protocol.T9_ONE_SIDED_95*statistics.stdev(ratios)/math.sqrt(protocol.PROCESSES))
        summary = dict(cell=cell["id"], upper95_ratio=upper, valid_durations=valid,
                       pass_cell=valid and upper <= 1,
                       costs={name: dict(median_ns=statistics.median(xs), min_ns=min(xs), max_ns=max(xs))
                              for name, xs in costs.items()})
        summaries.append(summary)
        with (args.out / "cell-results.jsonl").open("a") as f:
            f.write(json.dumps(summary) + "\n")
        print(cell["id"], "PASS" if summary["pass_cell"] else "FAIL", upper, flush=True)
    screen.load(args.prepared)
    result = dict(cells=summaries, all_cells_pass=all(c["pass_cell"] for c in summaries), after=host(args.cpu))
    (args.out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    if not result["all_cells_pass"]:
        raise SystemExit(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prepared", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--cpu", type=int, required=True)
    parser.add_argument("--cell")
    parser.add_argument("--worker", type=int)
    args = parser.parse_args()
    args.prepared, args.out = args.prepared.resolve(), args.out.resolve()
    if args.worker is None:
        qualify(args)
    else:
        worker(args)


if __name__ == "__main__":
    main()
