#!/usr/bin/env python3
"""Paired native qualification of the public normal-pair API on one host.

Uses the shared benchmark protocol, a prepared/observed screen directory,
and separate processes for each cell on x86 Linux or native Apple Silicon.
This does not replace consumer qualification. No compilation occurs during timing.
"""
import argparse
import ctypes as ct
import importlib.util
import json
import math
from pathlib import Path
import statistics
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import screen
import host as native_host

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
    return native_host.snapshot(cpu)


def timers(prepared, cell):
    native, functions = screen.load(prepared)
    library = ct.CDLL(str(native_host.product_path(prepared)))
    native.measure.argtypes = [ct.c_void_p, ct.POINTER(ct.c_uint64), ct.POINTER(screen.Pair),
                              ct.c_size_t, ct.c_uint64]
    native.measure.restype = ct.c_uint64
    native.measure_chain.argtypes = native.measure.argtypes
    native.measure_chain.restype = ct.c_uint64
    library.output_new.argtypes = [ct.c_size_t]
    library.output_new.restype = ct.c_void_p
    library.output_address.argtypes = [ct.c_void_p]
    library.output_address.restype = ct.c_size_t
    library.output_free.argtypes = [ct.c_void_p]
    library.output_free.restype = None
    library.measure_slice.argtypes = [ct.POINTER(ct.c_uint64), ct.POINTER(ct.c_uint64), ct.c_void_p,
                                     ct.c_size_t, ct.c_uint64, ct.c_uint8]
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

    class Storage:
        def __init__(self):
            self.handle = library.output_new(n)

        def __del__(self):
            library.output_free(self.handle)

    storage = Storage() if cell['kind'] == 'slice' else None

    def elapsed(name, count):
        f = functions[name]
        if cell["kind"] in ["scalar", "latency"]:
            timer = native.measure if cell["kind"] == "scalar" else native.measure_chain
            return timer(f, words, out, n, count)
        if cell["kind"] == "slice":
            selector = {"product": 0, "libm_direct": 1, "libm_folded": 2}[name]
            return library.measure_slice(first, second, storage.handle, n, count, selector)
        return library.measure_stream(f, n*count, cell["kind"] == "antithetic")
    if storage:
        elapsed.layout = dict(first=ct.addressof(first), second=ct.addressof(second),
                              output=library.output_address(storage.handle), pairs=n,
                              reuse="identical buffers for product and reference")
    elif cell['kind'] in ['scalar', 'latency']:
        elapsed.layout = dict(words=ct.addressof(words), output=ct.addressof(out), pairs=n,
                              reuse="identical buffers for product and reference")
    else:
        elapsed.layout = dict(seed=282, words_per_pair=2, generator="Xoshiro256++")
    return elapsed


def worker(args):
    native_host.configure(args.cpu, ct.CDLL(str(native_host.native_path(args.prepared))))
    manifest = json.loads((args.out / "qualification-manifest.json").read_text())
    cell = next(c for c in manifest["cells"] if c["id"] == args.cell)
    measure = timers(args.prepared, cell)
    counts = manifest["counts"][args.cell]
    result = dict(cell=cell, process=args.worker, before=host(args.cpu), layout=measure.layout,
                  warmups=[], samples=[])
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


def verify_prepared(prepared):
    if not (prepared / "observations.json").exists():
        raise RuntimeError("Run the independent observations before qualification")
    screen.load(prepared)
    if screen.digest(Path(__file__)) != screen.digest(prepared / "templates/qualify.py"):
        raise RuntimeError("Qualification runner differs from the frozen preparation")
    if screen.digest(HERE / "host.py") != screen.digest(prepared / "templates/host.py"):
        raise RuntimeError("Host adapter differs from the frozen preparation")
    if screen.digest(HERE / "screen.py") != screen.digest(prepared / "templates/screen.py"):
        raise RuntimeError("Preparation loader differs from the frozen preparation")
    if screen.digest(HERE.parent / "protocol.py") != screen.digest(prepared / "templates/protocol.py"):
        raise RuntimeError("Benchmark protocol differs from the frozen preparation")


def qualify(args):
    verify_prepared(args.prepared)
    args.out.mkdir(parents=True, exist_ok=False)
    native_host.configure(args.cpu, ct.CDLL(str(native_host.native_path(args.prepared))))
    manifest = dict(cells=cells(), counts={}, before=host(args.cpu),
                    prepared=str(args.prepared), prepared_manifest_sha256=screen.digest(args.prepared / "manifest.json"),
                    runner_sha256=screen.digest(Path(__file__)),
                    protocol_sha256=screen.digest(HERE.parent / "protocol.py"),
                    processes=protocol.PROCESSES, rounds=protocol.ROUNDS,
                    target_ns=protocol.TARGET_NS, minimum_ns=protocol.MINIMUM_NS,
                    upper95_t9=protocol.T9_ONE_SIDED_95,
                    decision="Every cell must have upper one-sided 95% ratio <= 1 and every timed sample >= minimum_ns; no retries or outlier removal",
                    interpretation=native_host.configuration()["interpretation"] + " Consumer qualification remains separate.")
    with (args.out / "calibration.jsonl").open("x", buffering=1) as log:
        for cell in manifest["cells"]:
            measure = timers(args.prepared, cell)
            counts = {}
            for name in ["product", cell["reference"]]:
                def record(kind, count, ns):
                    log.write(json.dumps(dict(cell=cell["id"], function=name, kind=kind,
                                              count=count, ns=ns)) + "\n")
                counts[name] = protocol.calibrate(lambda count: measure(name, count), record)
            # The same count also gives stream cells identical word prefixes,
            # rather than comparing different lengths of the seeded stream.
            common = max(counts.values())
            counts = {name: common for name in counts}
            manifest["counts"][cell["id"]] = counts
            print("Calibrated", cell["id"], flush=True)
    (args.out / "qualification-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    summaries = []
    for cell in manifest["cells"]:
        ratios, costs = [], {"product": [], cell["reference"]: []}
        valid = True
        for process in range(protocol.PROCESSES):
            subprocess.run([sys.executable, str(Path(__file__)), str(args.prepared),
                            "--out", str(args.out),
                            "--cell", cell["id"], "--worker", str(process)]
                           + (["--cpu", str(args.cpu)] if args.cpu is not None else []), check=True)
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
    parser.add_argument("--cpu", type=int, help="Required Linux CPU; omit on macOS")
    parser.add_argument("--cell")
    parser.add_argument("--worker", type=int)
    parser.add_argument("--profile", choices=["product", "strong"])
    parser.add_argument("--profile-count", type=int, default=20_000)
    args = parser.parse_args()
    native_host.validate_cpu(args.cpu)
    args.prepared, args.out = args.prepared.resolve(), args.out.resolve()
    if args.profile:
        if args.profile_count <= 0:
            parser.error("--profile-count must be positive")
        verify_prepared(args.prepared)
        native_host.configure(args.cpu, ct.CDLL(str(native_host.native_path(args.prepared))))
        cell = dict(kind="scalar", population="ordinary", n=4096, reference="libm_direct")
        measure = timers(args.prepared, cell)
        elapsed = measure(args.profile, args.profile_count)
        print(json.dumps(dict(purpose="instrumented profile only", function=args.profile,
                              ns=elapsed, pairs=4096*args.profile_count, host=host(args.cpu))))
    elif args.worker is None:
        qualify(args)
    else:
        worker(args)


if __name__ == "__main__":
    main()
