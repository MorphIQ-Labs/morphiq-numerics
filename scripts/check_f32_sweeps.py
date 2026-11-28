#!/usr/bin/env python3
"""Check every binary32 value, widened to binary64, in one shard of one operation.

Usage: python3 scripts/check_f32_sweeps.py NEW_OUTPUT_DIRECTORY --target NAME
           --operation NAME --shard I [--shards N] [--limit INPUTS]
       python3 scripts/check_f32_sweeps.py --schedule WEEK
       python3 scripts/check_f32_sweeps.py --matrix TARGET OPERATION
The 2^32 encodings of each one-argument operation are split into SHARDS equal
shards. A run is complete coverage of its shard only; --limit marks it partial.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess

if __package__:
    from .check_sweeps import OPERATIONS, ROOT, command_text, fixed_count, save_receipt
else:
    from check_sweeps import OPERATIONS, ROOT, command_text, fixed_count, save_receipt

TARGETS = ["elementary", "fast_elementary", "fast_normal", "strong_normal", "strong_density"]
SPACE = 2 ** 32
SHARDS = 64
CHUNK = 2 ** 20
WEEKLY = 64


def operations():
    """Every one-argument operation, in a stable order."""
    return [(target, op) for target in TARGETS for op in OPERATIONS[target]
            if fixed_count(target, op) == 0]


def shard_range(shard, shards):
    if shards < 1 or not 0 <= shard < shards or SPACE % shards:
        raise ValueError("shards must divide 2^32 and the shard index lie inside them")
    size = SPACE // shards
    return shard * size, (shard + 1) * size - 1


def chunks(first, last):
    return [(start, min(start + CHUNK - 1, last)) for start in range(first, last + 1, CHUNK)]


def schedule(week):
    """The units one weekly run covers; consecutive weeks rotate through all."""
    units = [(target, op, shard) for target, op in operations() for shard in range(SHARDS)]
    return [dict(zip(("target", "operation", "shard"), units[(week * WEEKLY + i) % len(units)]))
            for i in range(WEEKLY)]


def run_chunks(binary, mode_dir, target, selector, ranges, jobs, record):
    def one(bounds):
        first, last = bounds
        failure = mode_dir / f"{first:08x}.packet"
        result = subprocess.run(
            [str(binary), "--f32", target, str(selector), f"{first:08x}", f"{last:08x}", str(failure)],
            capture_output=True, text=True, check=False)
        # An exit status alone is insufficient: require the exact count.
        passed = result.returncode == 0 and result.stdout.strip() == str(last - first + 1)
        if not passed:
            (mode_dir / f"{first:08x}.log").write_text(result.stdout + result.stderr)
        return first, last, passed

    with ThreadPoolExecutor(jobs) as pool:
        for first, last, passed in pool.map(one, ranges):
            record(first, last, passed)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, nargs="?")
    parser.add_argument("--target", choices=TARGETS)
    parser.add_argument("--operation")
    parser.add_argument("--shard", type=int)
    parser.add_argument("--shards", type=int, default=SHARDS)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--schedule", type=int, metavar="WEEK")
    parser.add_argument("--matrix", nargs=2, metavar=("TARGET", "OPERATION"))
    args = parser.parse_args(argv)
    if args.schedule is not None:
        print(json.dumps(schedule(args.schedule)))
        return
    if args.matrix:
        if tuple(args.matrix) not in operations():
            parser.error("not a one-argument operation")
        print(json.dumps([dict(target=args.matrix[0], operation=args.matrix[1], shard=i)
                          for i in range(SHARDS)]))
        return
    if args.output is None or args.shard is None or (args.target, args.operation) not in operations():
        parser.error("an output directory, a one-argument operation and a shard are required")
    first, last = shard_range(args.shard, args.shards)
    if args.limit is not None:
        if args.limit < 1:
            parser.error("--limit must be positive")
        last = min(last, first + args.limit - 1)
    ranges = chunks(first, last)
    selector = OPERATIONS[args.target].index(args.operation)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)  # Never overwrite an earlier attempt.
    receipt = {
        "schema_version": 1, "status": "running", "partial": args.limit is not None,
        "target": args.target, "operation": args.operation,
        "shard": args.shard, "shards": args.shards,
        "first": f"{first:08x}", "last": f"{last:08x}",
        "revision": command_text("git", "rev-parse", "HEAD"),
        "working_tree": command_text("git", "status", "--porcelain"),
        "oracle_lock_sha256": hashlib.sha256((ROOT / "fuzz/Cargo.lock").read_bytes()).hexdigest(),
        "rustc": command_text("rustc", "-Vv"), "host": platform.platform(),
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "expected": 2 * (last - first + 1), "checked": 0, "failed": [],
    }
    save_receipt(output, receipt)
    try:
        for mode, features in [("scalar", ["--no-default-features"]),
                               ("simd", ["--no-default-features", "--features", "simd"])]:
            mode_dir = output / mode
            mode_dir.mkdir()
            with (output / f"build-{mode}.log").open("w") as log:
                subprocess.run(["cargo", "build", "--release", "--locked", "--manifest-path",
                                "fuzz/Cargo.toml", "--target-dir", "fuzz/target", "--bin", "sweep",
                                *features], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)

            def record(start, end, passed, mode=mode):
                if passed:
                    receipt["checked"] += end - start + 1
                else:
                    receipt["failed"].append(dict(mode=mode, first=f"{start:08x}", last=f"{end:08x}"))
                save_receipt(output, receipt)

            run_chunks(ROOT / "fuzz/target/release/sweep", mode_dir, args.target, selector,
                       ranges, args.jobs, record)
        if receipt["failed"] or receipt["checked"] != receipt["expected"]:
            raise RuntimeError(f"incomplete or failed coverage; see {output}")
        receipt["status"] = "passed"
        print(f"{args.target} {args.operation} shard {args.shard}: {receipt['checked']} checks passed")
    except BaseException:
        receipt["status"] = "failed"
        raise
    finally:
        save_receipt(output, receipt)


if __name__ == "__main__":
    main()
