#!/usr/bin/env python3
"""Require named numerical faults to fail their numerical tests in a clean copy.

Usage: python3 scripts/check_numerical_mutations.py OUTPUT_DIRECTORY
Only successful baseline tests followed by the specified numerical assertion
count as kills. Logs, patch identities and receipts survive every gate failure;
the isolated source tree is always removed, and the working checkout is untouched.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "scripts/mutations"
PACKAGES = ["morphiq-numerics", "morphiq-numerics-arch"]
REQUIRED_FAULTS = {
    "dropped-error-term", "wrong-rounding-direction", "off-by-one-exponent",
    "missed-carry", "perturbed-constant", "unsound-rounding-decision",
}


def catalog_entries(catalog):
    if catalog["schema"] != 1:
        raise ValueError("unsupported numerical catalog schema")
    entries = catalog["mutations"]
    if (not entries or any(not entry["id"] for entry in entries)
            or len({entry["id"] for entry in entries}) != len(entries)):
        raise ValueError("the numerical catalog must contain unique, nonempty fault IDs")
    faults = set()
    for entry in entries:
        expectation = entry.get("expectation", "numerical-rejection")
        if expectation == "equivalent-control":
            if entry["category"] != "equivalent-control" or not entry["derivation"]:
                raise ValueError("equivalent controls require a separate category and justification")
        elif expectation == "numerical-rejection" and entry["failure_contains"]:
            faults.add(entry["category"])
        else:
            raise ValueError(f"invalid numerical rejection expectation: {entry['id']}")
    missing = REQUIRED_FAULTS - faults
    if missing:
        raise ValueError(f"missing required numerical fault categories: {sorted(missing)}")
    return entries


def qualifies(text, code, entry, baseline):
    """A compiler error, timeout, ignored/absent test or other panic is not a kill."""
    name = re.escape(entry["test"])
    expect_pass = baseline or entry.get("expectation") == "equivalent-control"
    status = "ok" if expect_pass else "FAILED"
    summary = ("test result: ok. 1 passed; 0 failed; 0 ignored;" if expect_pass else
               "test result: FAILED. 0 passed; 1 failed; 0 ignored;")
    return (code == (0 if expect_pass else 101)
            and re.search(r"^running 1 test$", text, re.MULTILINE) is not None
            and re.search(rf"^test {name} \.\.\. {status}$", text, re.MULTILINE) is not None
            and summary in text
            and (expect_pass or entry["failure_contains"] in text))


def check_inventory(rows, floors):
    packages = Counter(row["package"] for row in rows)
    files = Counter(row["file"] for row in rows)
    for kind, counts in [("packages", packages), ("files", files)]:
        for name, minimum in floors[kind].items():
            if counts[name] < minimum:
                raise ValueError(f"mutation inventory below floor: {name}: {counts[name]} < {minimum}")
    return {"packages": dict(sorted(packages.items())), "files": dict(sorted(files.items()))}


def inventory(output):
    required = (ROOT / ".cargo/mutants-version").read_text().strip()
    version = subprocess.check_output(["cargo", "mutants", "--version"], text=True).strip()
    if version != f"cargo-mutants {required}":
        raise ValueError(f"install the pinned inventory tool: cargo install --locked cargo-mutants --version {required}")
    command = ["cargo", "mutants", "--no-config", "--list", "--json", "--all-features"]
    for package in PACKAGES:
        command += ["-p", package]
    path = output / "inventory.json"
    with path.open("w") as stream:
        subprocess.run(command, cwd=ROOT, stdout=stream, check=True, timeout=180)
    floors = json.loads((CATALOG / "inventory-floor.json").read_text())
    counts = check_inventory(json.loads(path.read_text()), floors)
    (output / "inventory-counts.json").write_text(json.dumps(counts, indent=2) + "\n")
    return version


def snapshot(work):
    names = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT
    ).decode().split("\0")
    for name in names:
        source = ROOT / name
        if name and source.is_file():
            dest = work / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, dest)


def run_test(work, output, entry, mode, baseline):
    label = f"{entry['id']}-{mode}-{'baseline' if baseline else 'mutant'}"
    command = ["cargo", "test", "--locked", "-p", entry["package"], "--no-default-features"]
    if mode == "simd":
        command += ["--features", "simd,std"]
    command += ["--lib"] if entry["target"] == "lib" else ["--test", entry["target"]]
    command += [entry["test"], "--", "--exact", "--test-threads=1", "--color", "never"]
    env = dict(os.environ, CARGO_TARGET_DIR=str(output / "build"), CARGO_TERM_COLOR="never")
    log = output / "logs" / f"{label}.log"
    timed_out = False
    with log.open("w") as stream:
        with subprocess.Popen(command, cwd=work, env=env, stdout=stream,
                              stderr=subprocess.STDOUT, start_new_session=True) as process:
            try:
                code = process.wait(timeout=300)
            except subprocess.TimeoutExpired:
                # Kill the whole owned Cargo/rustc/test group before removing
                # its source snapshot; a timeout is never a successful kill.
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                code = None
                timed_out = True
    return {"id": entry["id"], "mode": mode, "baseline": baseline, "command": command,
            "exit_status": code, "timed_out": timed_out, "log": str(log.relative_to(output)),
            "accepted": qualifies(log.read_text(), code, entry, baseline)}


def run(output):
    if output.exists() and any(output.iterdir()):
        raise ValueError(f"choose a fresh output directory to preserve earlier receipts: {output}")
    output.mkdir(parents=True, exist_ok=True)
    (output / "logs").mkdir(exist_ok=True)
    receipt = {"source": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
               "worktree_status": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True),
               "toolchain": subprocess.check_output(["rustc", "--version"], cwd=ROOT, text=True).strip(),
               "runs": [], "passed": False}
    try:
        entries = catalog_entries(json.loads((CATALOG / "catalog.json").read_text()))
        receipt["inventory_tool"] = inventory(output)
        with tempfile.TemporaryDirectory(prefix="source-", dir=output) as directory:
            work = Path(directory)
            snapshot(work)
            # Prevent Git from discovering and applying patches to the parent
            # checkout when OUTPUT_DIRECTORY is beneath its ignored target/.
            subprocess.run(["git", "init", "--quiet", str(work)], check=True)
            for entry in entries:
                patch = CATALOG / entry["patch"]
                owner = entry["source"]
                if not owner.startswith("crates/morphiq-numerics/src/") or "/tests" in owner:
                    raise ValueError(f"fault must target production arithmetic: {owner}")
                changed = subprocess.check_output(["git", "apply", "--numstat", str(patch)], cwd=work, text=True)
                if [line.split("\t")[-1] for line in changed.splitlines()] != [owner]:
                    raise ValueError(f"{entry['id']}: patch must touch only its declared source")
                original = (work / owner).read_bytes()
                identity = {"patch_sha256": hashlib.sha256(patch.read_bytes()).hexdigest(),
                            "source_sha256": hashlib.sha256(original).hexdigest()}
                for mode in ["scalar", "simd"]:
                    for baseline in [True, False]:
                        try:
                            if not baseline:
                                subprocess.run(["git", "apply", "--check", str(patch)], cwd=work, check=True)
                                subprocess.run(["git", "apply", str(patch)], cwd=work, check=True)
                            result = run_test(work, output, entry, mode, baseline)
                            receipt["runs"].append(dict(result, **identity,
                                                       expectation=entry.get("expectation", "numerical-rejection")))
                            print(entry["id"], mode, "baseline" if baseline else "mutant",
                                  "PASS" if result["accepted"] else "FAIL", flush=True)
                            if not result["accepted"]:
                                raise ValueError(f"{entry['id']} {mode}: unexpected named test outcome; see {result['log']}")
                        finally:
                            (work / owner).write_bytes(original)
        receipt["passed"] = True
    except Exception as error:
        receipt["error"] = str(error)
        raise
    finally:
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    run(parser.parse_args().output.resolve())
