#!/usr/bin/env python3
"""Prepare the bounded log-CDF comparison with the existing native timer and runner.

Comparators: Risk's own `log_norm_cdf` (a pinned checkout, built here as a C-ABI
library) for scalar throughput, dependent latency and the 52-value packet on
three populations, and the strong `normal::log_norm_cdf` as the unchanged
control. SciPy `log_ndtr` is available as a diagnostic reference through
qualify-cell.py. All source/build/oracle work must finish before running
run-qualification.py; timings exclude builds, profiles and oracles.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import struct
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
POPULATIONS = dict(ordinary=(-3.0, 3.0), wide=(-8.0, 8.0), tail=(-22.0, -8.0))


def bank(lo, hi, n=52):
    # Off the dyadic grid, strictly inside the population.
    return [struct.pack('>d', lo + (hi - lo) * (i + 0.37) / (n + 0.11)).hex() for i in range(n)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--risk', type=Path, required=True, help='ferro-risk checkout (crates/ferro-risk)')
    ap.add_argument('--cpu', type=int, default=2)
    args = ap.parse_args()
    if (platform.system(), platform.machine()) != ('Linux', 'x86_64'):
        ap.error('This adapter requires native x86-64 Linux')
    out = args.out.resolve()
    out.relative_to((ROOT / 'target').resolve())
    risk = args.risk.resolve()
    if not (risk / 'crates/ferro-risk/Cargo.toml').is_file():
        ap.error('--risk must point at a ferro-risk checkout')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        ap.error('Commit the candidate before preparing a comparison')
    risk_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=risk, text=True).strip()
    risk_dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=risk, text=True).strip())
    out.mkdir(parents=True, exist_ok=False)
    (out / 'bin').mkdir()
    for name in ['qualify-cell.py', 'run-qualification.py']:
        shutil.copy2(HERE / name, out / name)
    for name in ['inputs.py', 'protocol.py']:
        shutil.copy2(HERE.parent / name, out / name)
    (out / 'config.json').write_text(json.dumps(dict(cpu=args.cpu)) + '\n')
    shutil.copytree(HERE / 'log-cdf-wrapper', out / 'wrapper')
    (out / 'wrapper/Cargo.toml').write_text('''[package]
name="log-cdf-bench-wrapper"
version="0.0.0"
edition="2024"
[workspace]
[lib]
crate-type=["cdylib"]
[dependencies]
morphiq-numerics={path=''' + json.dumps(str(ROOT / 'crates/morphiq-numerics')) + ''',features=["simd","std"]}
[profile.release]
lto="thin"
codegen-units=1
''')
    shutil.copytree(HERE / 'risk-log-cdf-wrapper', out / 'risk-wrapper')
    (out / 'risk-wrapper/Cargo.toml').write_text('''[package]
name="risk-log-cdf-bench-wrapper"
version="0.0.0"
edition="2024"
[workspace]
[lib]
crate-type=["cdylib"]
[dependencies]
ferro-risk={path=''' + json.dumps(str(risk / 'crates/ferro-risk')) + '''}
[profile.release]
lto="thin"
codegen-units=1
''')
    commands = []

    def run(command, **kwargs):
        commands.append(command)
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        subprocess.run(command, check=True, **kwargs)

    env = dict(os.environ, RUSTFLAGS='')
    for name in ['CARGO_ENCODED_RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
                 'CARGO_BUILD_TARGET', 'CARGO_BUILD_RUSTFLAGS']:
        env.pop(name, None)
    run(['cargo', 'build', '--release', '--manifest-path', str(out / 'wrapper/Cargo.toml')],
        env=dict(env, CARGO_TARGET_DIR=str(out / 'build')))
    run(['cargo', 'build', '--release', '--manifest-path', str(out / 'risk-wrapper/Cargo.toml')],
        env=dict(env, CARGO_TARGET_DIR=str(out / 'risk-build')))
    # The timers without their SLEEF comparators: this comparison has none.
    for timer in ['native-matrix', 'native-cache']:
        run(['cc', '-O3', '-fPIC', '-shared', '-ffp-contract=off', '-DNO_SLEEF',
             str(HERE / (timer + '.c')), '-o', str(out / 'bin' / (timer + '.so'))])
    product = out / 'build/release/liblog_cdf_bench_wrapper.so'
    # The comparator library lives under references/, which freeze.py hashes.
    (out / 'references').mkdir()
    risk_product = out / 'references/librisk_log_norm_cdf.so'
    shutil.copy2(out / 'risk-build/release/librisk_log_cdf_bench_wrapper.so', risk_product)
    (out / 'final-bin').mkdir()
    shutil.copy2(product, out / 'final-bin/control.so')
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    cells = []
    for population, (lo, hi) in POPULATIONS.items():
        words = bank(lo, hi)
        path = out / (population + '.json')
        path.write_text(json.dumps(words) + '\n')
        entry = dict(file=str(path), length=52,
                     sha256=hashlib.sha256(bytes.fromhex(''.join(words))).hexdigest())
        for kind in ['scalar', 'latency', 'vector']:
            cells.append(dict(id=f'log-cdf-{population}-{kind}', primitive='log_cdf', backend='auto',
                              length=52, population=population, kind=kind, reference='risk_log_norm_cdf',
                              reference_product=str(risk_product), input=entry, product=str(product),
                              required_parity=True, control=False))
        # The unchanged strong entry against itself: a drift control.
        cells.append(dict(id=f'log-cdf-{population}-control', primitive='log_cdf', backend='auto',
                          length=52, population=population, kind='vector', reference='control',
                          input=entry, product=str(product), required_parity=False, control=True))
    manifest = dict(scope='Bounded log-CDF against Risk log_norm_cdf on three 52-value populations; '
                          'full #192 qualification (ARM, lengths, mixed/fallback banks) remains separate',
                    source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                    risk_commit=risk_commit, risk_dirty=risk_dirty,
                    builds=[dict(name='auto', sha256=digest(product))],
                    reference_builds=[dict(name='risk_log_norm_cdf', sha256=digest(risk_product))],
                    cells=cells, protocol=dict(upper95_t9=1.8331129326536335))
    (out / 'qualification-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(out)


if __name__ == '__main__':
    main()
