#!/usr/bin/env python3
"""Whether a change can alter what the formal lane checks.

The lane (scripts/check_formal.sh) checks the proofs, the files they are bound
to, and the extracted kernels against the Rust library on a corpus the library
writes. A change that touches none of those cannot change its result, so a pull
request that touches none of them reports the lane as not affected instead of
spending hours re-proving it. A push to the default branch runs the lane in
full whatever this says.

It answers "affected" whenever it is not sure: any path under formal/, any file
a binding manifest lists, any library source that is not a test file, the
workspace manifests, the lane's scripts and toolchain pins, and this workflow.

usage: formal_relevant.py --changed FILE
prints `affected: PATH` or `not affected`, and exits 0 either way.
"""
import argparse
import glob
import os
import sys

ALWAYS = (
    "formal/",
    "scripts/check_formal",
    "scripts/formal_",
    "scripts/write_gappa_proofs.sh",
    ".cargo/coq-",
    ".github/workflows/ci.yml",
    "Cargo.toml",
    "Cargo.lock",
    "rust-toolchain",
    "crates/reference/src/",
    "crates/reference/Cargo.toml",
)
LIBRARY = "crates/morphiq-numerics/src/"


def bound_files(root="."):
    """Every path a binding manifest lists."""
    paths = set()
    for manifest in glob.glob(os.path.join(root, "formal", "**", "binding.sha256"), recursive=True):
        with open(manifest) as handle:
            for line in handle:
                parts = line.split(None, 1)
                if len(parts) == 2:
                    paths.add(parts[1].strip())
    return paths


def is_test_source(path):
    """A file of the library that only the test build compiles."""
    name = os.path.basename(path)
    return name == "tests.rs" or name.endswith("_tests.rs") or "/tests/" in path


def first_affecting(paths, bound):
    """The first changed path that can alter the lane's result, or None."""
    for path in paths:
        path = path.strip()
        if not path:
            continue
        if path.startswith(ALWAYS) or path in bound:
            return path
        if path.startswith(LIBRARY) and not is_test_source(path):
            return path
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--changed", required=True)
    parser.add_argument("--root", default=".")
    args = parser.parse_args()
    with open(args.changed) as handle:
        paths = handle.read().split("\n")
    path = first_affecting(paths, bound_files(args.root))
    print("not affected" if path is None else f"affected: {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
