#!/usr/bin/env python3
"""Run declared boundary windows; retain exact coverage and failures.

Usage: python3 scripts/check_sweeps.py NEW_OUTPUT_DIRECTORY [--profile smoke]
       [--target NAME ...]
       python3 scripts/check_sweeps.py --list
Full windows are versioned in fuzz/sweeps/TARGET.json. Smoke checks at most five
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
MANIFESTS = ROOT / "fuzz/sweeps"
# Operation selectors of each fuzz target's packet format (fuzz/README.md).
OPERATIONS = {
    "elementary": ["exp", "exp2", "expm1", "ln", "ln_1p", "log2", "log10", "sin",
                   "cos", "tan", "sqrt", "asin", "asinh", "atan2"],
    "fast_elementary": ["exp", "exp_coarse", "ln"],
    "fast_normal": ["erfcx", "cdf", "log_cdf"],
    "strong_normal": ["erfcx", "cdf", "log_cdf"],
    "strong_density": ["pdf", "ccdf", "centered", "log_pdf"],
    # Targets with one packet layout; the window varies its first argument.
    "bivariate": ["cdf"],
    "reductions": ["log_space"],
    "arithmetic": ["double_word"],
    "structures": ["interval"],
    "streams": ["words"],
}
# Fixed words each record takes after the swept one.
FIXED = {"atan2": 1, "cdf_bivariate": 2, "log_space": 1, "double_word": 3, "interval": 1, "words": 1}
INTEGER_TARGETS = {"streams"}


def fixed_count(target, operation):
    return FIXED.get("cdf_bivariate" if target == "bivariate" else operation, 0)


def load_windows(path, profile, target):
    operations = OPERATIONS[target]
    document = json.loads(path.read_text())
    if document["schema_version"] != 1 or not document["windows"]:
        raise ValueError("unsupported or empty sweep manifest")
    if profile not in ("full", "smoke"):
        raise ValueError("unknown sweep profile")
    windows, names, intervals = [], set(), {}
    for row in document["windows"]:
        name, op = row["name"], row["operation"]
        if not re.fullmatch(r"[a-z][a-z0-9_-]*", name) or name in names:
            raise ValueError(f"invalid or duplicate window name: {name}")
        names.add(name)
        if op not in operations or not row["source"]:
            raise ValueError(f"missing operation/source: {name}")
        if any(not re.fullmatch(r"[0-9a-f]{16}", row[key]) for key in ("first", "last", "anchor")):
            raise ValueError(f"invalid binary64 encoding: {name}")
        fixed = row.get("fixed", [])
        if len(fixed) != fixed_count(target, op) or any(
                not re.fullmatch(r"[0-9a-f]{16}", word) for word in fixed):
            raise ValueError(f"wrong fixed words for {op}: {name}")
        first, last, anchor = (int(row[key], 16) for key in ("first", "last", "anchor"))
        if not first <= anchor <= last or target not in INTEGER_TARGETS and first >> 63 != last >> 63:
            raise ValueError(f"unordered or sign-crossing window: {name}")
        if target not in INTEGER_TARGETS and any((bits >> 52) & 0x7ff == 0x7ff for bits in (first, last)):
            raise ValueError(f"nonfinite window: {name}")
        if last - first >= 1_048_576:
            raise ValueError(f"window exceeds one million inputs: {name}")
        seen = intervals.setdefault((op, tuple(fixed)), [])
        if any(first <= end and start <= last for start, end in seen):
            raise ValueError(f"overlapping windows for {op}: {name}")
        seen.append((first, last))
        if profile == "smoke":
            first, last = max(first, anchor - 2), min(last, anchor + 2)
        windows.append({**row, "target": target, "selector": operations.index(op),
                        "fixed": fixed, "first": f"{first:016x}", "last": f"{last:016x}",
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
        stem = f'{row["target"]}-{row["name"]}'
        failure = mode_dir / (stem + ".packet")
        command = [str(binary), row["target"], str(row["selector"]), row["first"], row["last"],
                   str(failure), *row["fixed"]]
        with (mode_dir / (stem + ".stderr.log")).open("w") as log:
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=log, text=True, check=False)
        (mode_dir / (stem + ".stdout.log")).write_text(result.stdout)
        # An exit status alone is insufficient: require the enumerator's exact
        # completion count. Interrupted/failed windows contribute no coverage.
        if result.returncode != 0 or result.stdout.strip() != str(row["expected"]):
            entry["status"] = "failed"
            save_receipt(output, receipt)
            raise RuntimeError(f"{mode}/{stem} failed or returned an incomplete count; see {mode_dir}")
        entry.update(status="passed", checked=row["expected"])
        receipt["checked"] += row["expected"]
        save_receipt(output, receipt)
        print(f"{mode}/{stem}: {row['expected']} inputs passed", flush=True)


def command_text(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, nargs="?")
    parser.add_argument("--profile", choices=["full", "smoke"], default="full")
    parser.add_argument("--target", action="append", choices=sorted(OPERATIONS))
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    if args.list:
        print("\n".join(OPERATIONS))
        return
    if args.output is None:
        parser.error("an output directory is required")
    targets = args.target or list(OPERATIONS)
    manifests = {target: MANIFESTS / f"{target}.json" for target in targets}
    windows = [row for target, path in manifests.items()
               for row in load_windows(path, args.profile, target)]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)  # Never overwrite an earlier attempt.
    digests = {}
    for target, path in manifests.items():
        manifest_bytes = path.read_bytes()
        (output / f"manifest-{target}.json").write_bytes(manifest_bytes)
        digests[target] = hashlib.sha256(manifest_bytes).hexdigest()
    receipt = {
        "schema_version": 1, "status": "running", "profile": args.profile,
        "revision": command_text("git", "rev-parse", "HEAD"),
        "working_tree": command_text("git", "status", "--porcelain"),
        "manifest_sha256": digests,
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
                                "fuzz/Cargo.toml", "--target-dir", "fuzz/target", "--bin", "sweep",
                                *features], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
            binary = ROOT / "fuzz/target/release/sweep"
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
