#!/usr/bin/env python3
"""Refresh the independent fuzz lockfile on the PR returned by release-plz.

Run at the repository root with release-plz release-pr -o json output as argv[1].
Use ordinary fast-forward pushes so a concurrent branch update is never lost.
"""
import json
from pathlib import Path
import subprocess
import sys
import tomllib


def run(*args, capture=False):
    return subprocess.check_output(args, text=True).strip() if capture else subprocess.run(args, check=True)


def refresh(output):
    prs = json.loads(Path(output).read_text())["prs"]
    if not prs:
        print("No release PR was opened or updated; no fuzz lockfile to refresh.")
        return
    if len(prs) != 1:
        raise ValueError("expected one workspace release PR")
    branch = prs[0]["head_branch"]
    if not branch.startswith("release-plz-") or prs[0]["base_branch"] != "main":
        raise ValueError("expected a release-plz-* branch targeting main")
    run("git", "check-ref-format", "--branch", branch)
    if run("git", "status", "--porcelain", capture=True):
        raise ValueError("release lockfile refresh requires a clean checkout")
    run("git", "fetch", "origin", f"refs/heads/{branch}")
    run("git", "checkout", "--detach", "FETCH_HEAD")
    lock = Path("fuzz/Cargo.lock")
    expected = tomllib.loads(lock.read_text())
    version = tomllib.loads(Path("Cargo.toml").read_text())["workspace"]["package"]["version"]
    for package in expected["package"]:
        if package["name"] in {"morphiq-numerics", "morphiq-numerics-arch"} and "source" not in package:
            package["version"] = version
    run("cargo", "update", "--manifest-path", "fuzz/Cargo.toml", "--workspace")
    if tomllib.loads(lock.read_text()) != expected:
        raise ValueError("fuzz lockfile changed beyond the two local release versions; inspect before committing")
    changed = run("git", "diff", "--name-only", "HEAD", capture=True).splitlines()
    if not changed:
        print("Fuzz lockfile already matches the release.")
        return
    if changed != ["fuzz/Cargo.lock"]:
        raise ValueError(f"unexpected files changed during lockfile refresh: {changed}")
    run("git", "add", "fuzz/Cargo.lock")
    run("git", "commit", "-m", "chore: refresh fuzz lockfile for release")
    run("git", "push", "origin", f"HEAD:refs/heads/{branch}")


if __name__ == "__main__":
    refresh(sys.argv[1])
