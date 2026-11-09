#!/usr/bin/env python3
"""Verify the two release archives and an external consumer; never publish.

Run from a clean committed checkout with an unused output directory. The only
staging changes enable the two publication flags so Cargo can use its built-in
workspace package registry before the crates exist on crates.io. Source guards
and release-plz configuration are unchanged.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

CRATES = ("morphiq-numerics-arch", "morphiq-numerics")
ROOT = Path(__file__).resolve().parents[1]


def run(*args, cwd=ROOT, **kwargs):
    subprocess.run(args, cwd=cwd, check=True, **kwargs)


def bootstrap_manifest(path):
    before = tomllib.loads(path.read_text())
    allowed = before["package"].get("publish", True)
    if allowed is False:
        text, count = re.subn(r"(?m)^publish\s*=\s*false\s*(?:#[^\n]*)?$",
                              'publish = true', path.read_text())
        expected = copy.deepcopy(before)
        expected["package"]["publish"] = True
        if count != 1 or tomllib.loads(text) != expected:
            raise ValueError(f"cannot isolate the package publication flag in {path}")
        path.write_text(text)
    elif allowed is not True:
        raise ValueError(f"unexpected publication registry in {path}: {allowed}")


def check_publishable(metadata):
    if any(p["publish"] is not None and p["publish"] != [] for p in metadata["packages"]):
        raise ValueError("release manifests must use boolean publication flags, not registry lists")
    publishable = {p["name"] for p in metadata["packages"] if p["publish"] is None}
    if publishable != set(CRATES):
        raise ValueError(f"publishable workspace packages differ from the release allowlist: {publishable}")


def check_archive(path, name, version, root):
    prefix = f"{name}-{version}/"
    with tarfile.open(path) as archive:
        def read(relative):
            member = archive.getmember(prefix + relative)
            if not member.isfile():
                raise ValueError(f"package member is not a file: {relative}")
            return archive.extractfile(member).read()
        for license_name in ("LICENSE-MIT", "LICENSE-APACHE"):
            if read(license_name) != (root / license_name).read_bytes():
                raise ValueError(f"{name}: packaged {license_name} differs from the root license")
        readme = read("README.md").decode()
        if not readme.strip() or re.search(r"\]\((?!https://|#)[^)]+\)", readme):
            raise ValueError(f"{name}: README must be nonempty and its links work outside the repository")
        manifest = tomllib.loads(read("Cargo.toml").decode())
        package = manifest["package"]
        if (package["name"], package["version"], package["license"], package["readme"]) != (
                name, version, "MIT OR Apache-2.0", "README.md"):
            raise ValueError(f"{name}: incorrect normalized package metadata")
        if not package["metadata"]["docs"]["rs"]["all-features"]:
            raise ValueError(f"{name}: docs.rs must document all features")
        if manifest.get("dev-dependencies") or manifest.get("build-dependencies") or manifest.get("target"):
            raise ValueError(f"{name}: unexpected tooling or target-specific dependencies")
        dependencies = manifest.get("dependencies", {})
        if name == "morphiq-numerics-arch":
            if dependencies:
                raise ValueError("the architecture package must remain dependency-free")
        else:
            if set(dependencies) != {"morphiq-numerics-arch"}:
                raise ValueError("the library must depend only on its optional architecture package")
            arch = dependencies["morphiq-numerics-arch"]
            if arch != {"version": version, "optional": True}:
                raise ValueError(f"the packaged architecture dependency is not registry-ready: {arch}")
            if read("THIRD_PARTY_NOTICES.md") != (root / "crates" / name / "THIRD_PARTY_NOTICES.md").read_bytes():
                raise ValueError("the packaged third-party notices differ from their source")
    return dict(crate=name, version=version, bytes=path.stat().st_size)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "target/package-check")
    args = parser.parse_args()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT).strip():
        parser.error("package verification requires a clean committed checkout")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    stage = out / "source"
    stage.mkdir()
    with (out / "source.tar").open("wb") as archive:
        run("git", "archive", "HEAD", stdout=archive)
    with tarfile.open(out / "source.tar") as archive:
        archive.extractall(stage, filter="data")
    version = tomllib.loads((stage / "Cargo.toml").read_text())["workspace"]["package"]["version"]
    for name in CRATES:
        bootstrap_manifest(stage / "crates" / name / "Cargo.toml")
    artifacts = out / "artifacts"
    metadata = json.loads(subprocess.check_output(
        ["cargo", "metadata", "--locked", "--format-version", "1", "--no-deps"], cwd=stage))
    check_publishable(metadata)
    run("cargo", "publish", "--dry-run", "--locked", "--workspace", "--all-features",
        "--target-dir", str(artifacts), cwd=stage)
    results = [check_archive(artifacts / "package/tmp-crate" / f"{name}-{version}.crate", name, version, stage)
               for name in CRATES]

    # Consume only Cargo's unpacked archives. The registry dependency was
    # verified by Cargo's publish dry run above; this offline patch supplies that same
    # packaged dependency while it has no public registry entry yet.
    consumer = out / "consumer"
    (consumer / "src").mkdir(parents=True)
    (consumer / "src/main.rs").write_text('''use morphiq_numerics::{elementary, fast, normal};
fn main() {
    assert_eq!(elementary::exp(0.0), 1.0);
    assert_eq!(elementary::ln(1.0).to_bits(), 0.0_f64.to_bits());
    assert_eq!(elementary::sqrt(4.0), 2.0);
    assert_eq!(normal::norm_cdf(0.0), 0.5);
    let input = [-744.0, -10.0, -1.0, -0.0, 0.0, 0.1, 1.0, 2.0, 700.0,
                 0.5, -0.5, 3.0, -3.0, 4.0, 8.0, 16.0, 32.0];
    for len in [0, 1, 3, 8, 9, 17] {
        let mut out = [0.0; 17];
        elementary::exp_slice(&input[..len], &mut out[..len]);
        for i in 0..len { assert_eq!(out[i].to_bits(), elementary::exp(input[i]).to_bits()); }
        fast::elementary::exp_slice(&input[..len], &mut out[..len]);
        for i in 0..len { assert_eq!(out[i].to_bits(), fast::elementary::exp(input[i]).to_bits()); }
    }
}
''')
    for features in (["simd", "std"], [], ["std"], ["simd"]):
        manifest = '''[package]
name = "package-consumer"
version = "0.0.0"
edition = "2024"
publish = false
[workspace]
[dependencies.morphiq-numerics]
path = %s
features = %s
[patch.crates-io.morphiq-numerics-arch]
path = %s
''' % (json.dumps(str(artifacts / "package" / f"morphiq-numerics-{version}")), json.dumps(features),
       json.dumps(str(artifacts / "package" / f"morphiq-numerics-arch-{version}")))
        (consumer / "Cargo.toml").write_text(manifest)
        run("cargo", "generate-lockfile", "--offline", cwd=consumer)
        run("cargo", "run", "--offline", "--locked", cwd=consumer)
        if features == ["simd", "std"]:
            env = dict(os.environ, RUSTDOCFLAGS="-D warnings")
            run("cargo", "doc", "--offline", "--locked", cwd=consumer, env=env)
    receipt = dict(source=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                   packages=results, consumer_features=["simd,std", "default", "std", "simd"],
                   registry_uploaded=False)
    (out / "verified.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Package and external-consumer verification passed; nothing was uploaded.")


if __name__ == "__main__":
    main()
