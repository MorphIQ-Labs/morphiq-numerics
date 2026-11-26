#!/usr/bin/env python3
"""Run declared normal boundary windows; retain exact coverage and failures.

Usage: python3 scripts/check_normal_sweeps.py NEW_OUTPUT_DIRECTORY [--profile smoke]
Full windows are versioned in fuzz/sweeps/normal.json. Smoke checks at most five
encodings around each anchor and is explicitly recorded as partial coverage.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "fuzz/sweeps/normal.json"
OPERATIONS = {"erfcx": 0, "cdf": 1, "log_cdf": 2}


def load_windows(path, profile):
    document = json.loads(path.read_text())
    if document["schema_version"] != 1 or not document["windows"]:
        raise ValueError("unsupported or empty sweep manifest")
    if profile not in ("full", "smoke"):
        raise ValueError("unknown sweep profile")
    windows, names, intervals = [], set(), {op: [] for op in OPERATIONS}
    for row in document["windows"]:
        name, op = row["name"], row["operation"]
        if not re.fullmatch(r"[a-z][a-z0-9_-]*", name) or name in names:
            raise ValueError(f"invalid or duplicate window name: {name}")
        names.add(name)
        if op not in OPERATIONS or not row["source"]:
            raise ValueError(f"missing operation/source: {name}")
        if any(not re.fullmatch(r"[0-9a-f]{16}", row[key]) for key in ("first", "last", "anchor")):
            raise ValueError(f"invalid binary64 encoding: {name}")
        first, last, anchor = (int(row[key], 16) for key in ("first", "last", "anchor"))
        if not first <= anchor <= last or first >> 63 != last >> 63:
            raise ValueError(f"unordered or sign-crossing window: {name}")
        if any((bits >> 52) & 0x7ff == 0x7ff for bits in (first, last)):
            raise ValueError(f"nonfinite window: {name}")
        if last - first >= 1_048_576:
            raise ValueError(f"window exceeds one million inputs: {name}")
        if any(first <= end and start <= last for start, end in intervals[op]):
            raise ValueError(f"overlapping windows for {op}: {name}")
        intervals[op].append((first, last))
        if profile == "smoke":
            first, last = max(first, anchor - 2), min(last, anchor + 2)
        windows.append({**row, "first": f"{first:016x}", "last": f"{last:016x}",
                        "expected": last - first + 1})
    return windows


def save_receipt(output, receipt):
    temporary = output / "coverage.tmp"
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(output / "coverage.json")


def run_windows(binary, output, mode, windows, receipt):
    mode_dir = output / mode
    mode_dir.mkdir()
    for row in windows:
        entry = {**row, "mode": mode, "status": "running", "checked": 0}
        receipt["windows"].append(entry)
        save_receipt(output, receipt)
        failure = mode_dir / (row["name"] + ".packet")
        command = [str(binary), str(OPERATIONS[row["operation"]]), row["first"], row["last"], str(failure)]
        with (mode_dir / (row["name"] + ".stderr.log")).open("w") as log:
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=log, text=True, check=False)
        (mode_dir / (row["name"] + ".stdout.log")).write_text(result.stdout)
        # An exit status alone is insufficient: require the enumerator's exact
        # completion count. Interrupted/failed windows contribute no coverage.
        if result.returncode != 0 or result.stdout.strip() != str(row["expected"]):
            entry["status"] = "failed"
            save_receipt(output, receipt)
            raise RuntimeError(f"{mode}/{row['name']} failed or returned an incomplete count; see {mode_dir}")
        entry.update(status="passed", checked=row["expected"])
        receipt["checked"] += row["expected"]
        save_receipt(output, receipt)
        print(f"{mode}/{row['name']}: {row['expected']} inputs passed", flush=True)


def command_text(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--profile", choices=["full", "smoke"], default="full")
    args = parser.parse_args()
    windows = load_windows(MANIFEST, args.profile)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)  # Never overwrite an earlier attempt.
    manifest_bytes = MANIFEST.read_bytes()
    (output / "manifest.json").write_bytes(manifest_bytes)
    receipt = {
        "schema_version": 1, "status": "running", "profile": args.profile,
        "revision": command_text("git", "rev-parse", "HEAD"),
        "working_tree": command_text("git", "status", "--porcelain"),
        "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
        "oracle_lock_sha256": hashlib.sha256((ROOT / "fuzz/Cargo.lock").read_bytes()).hexdigest(),
        "rustc": command_text("rustc", "-Vv"), "host": platform.platform(),
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "modes": {"scalar": ["--no-default-features"],
                  "simd": ["--no-default-features", "--features", "simd"]},
        "expected": 2 * sum(row["expected"] for row in windows), "checked": 0, "windows": [],
    }
    save_receipt(output, receipt)
    try:
        for mode, features in receipt["modes"].items():
            with (output / f"build-{mode}.log").open("w") as log:
                subprocess.run(["cargo", "build", "--release", "--locked", "--manifest-path",
                                "fuzz/Cargo.toml", "--target-dir", "fuzz/target", "--bin", "normal-sweep",
                                *features], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
            binary = ROOT / "fuzz/target/release/normal-sweep"
            run_windows(binary, output, mode, windows, receipt)
        if receipt["checked"] != receipt["expected"]:
            raise RuntimeError("incomplete campaign coverage")
        receipt["status"] = "passed"
    except BaseException:
        receipt["status"] = "failed"
        raise
    finally:
        save_receipt(output, receipt)


if __name__ == "__main__":
    main()
