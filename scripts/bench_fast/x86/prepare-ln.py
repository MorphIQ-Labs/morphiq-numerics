#!/usr/bin/env python3
"""Prepare a focused ln comparison using the existing native timer and runner.

This selects three ordinary-input cells, not the full #193 acceptance matrix.
All source/build/oracle work must finish before running run-qualification.py.
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


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--reference-bin', type=Path, required=True)
    ap.add_argument('--cpu', type=int, default=2)
    args = ap.parse_args()
    if (platform.system(), platform.machine()) != ('Linux', 'x86_64'):
        ap.error('This adapter requires native x86-64 Linux with AVX-512F')
    cpu_flags = Path('/proc/cpuinfo').read_text()
    if 'avx512f' not in cpu_flags or 'fma' not in cpu_flags:
        ap.error('The selected SLEEF packet requires AVX-512F and FMA')
    out = args.out.resolve()
    out.relative_to((ROOT / 'target').resolve())
    refs = args.reference_bin.resolve()
    if not (refs / 'libsleef.so.3').is_file() or not (refs / 'libsleef.so').is_file():
        ap.error('Pinned SLEEF shared libraries are required')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        ap.error('Commit the candidate before preparing a comparison')
    out.mkdir(parents=True, exist_ok=False)
    (out / 'bin').mkdir()
    (out / 'references').symlink_to(refs, target_is_directory=True)
    shutil.copytree(HERE / 'ln-wrapper', out / 'wrapper')
    for name in ['qualify-cell.py', 'run-qualification.py']:
        shutil.copy2(HERE / name, out / name)
    for name in ['inputs.py', 'protocol.py']:
        shutil.copy2(HERE.parent / name, out / name)
    (out / 'config.json').write_text(json.dumps(dict(cpu=args.cpu)) + '\n')
    (out / 'wrapper/Cargo.toml').write_text('''[package]
name="ln-bench-wrapper"
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
    commands = []

    def run(command, **kwargs):
        commands.append(command)
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        subprocess.run(command, check=True, **kwargs)

    env = dict(os.environ, CARGO_TARGET_DIR=str(out / 'build'), RUSTFLAGS='')
    for name in ['CARGO_ENCODED_RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
                 'CARGO_BUILD_TARGET', 'CARGO_BUILD_RUSTFLAGS']:
        env.pop(name, None)
    run(['cargo', 'build', '--release', '--manifest-path', str(out / 'wrapper/Cargo.toml')], env=env)
    for timer in ['native-matrix', 'native-cache']:
        command = ['cc', '-O3', '-fPIC', '-shared', '-ffp-contract=off', str(HERE / (timer + '.c'))]
        if timer == 'native-matrix':
            command += ['-L' + str(refs), '-Wl,-rpath,' + str(refs), '-lsleef']
        run(command + ['-o', str(out / 'bin' / (timer + '.so'))])
    words = [struct.pack('>d', .5 + 1.5*i/51).hex() for i in range(52)]
    bank = out / 'ordinary.json'
    bank.write_text(json.dumps(words) + '\n')
    product = out / 'build/release/libln_bench_wrapper.so'
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    cells = [dict(id='ln-' + kind, primitive='ln', backend='auto', length=52,
                  population='ordinary', kind=kind, reference=reference,
                  input=dict(file=str(bank), length=52,
                             sha256=hashlib.sha256(bytes.fromhex(''.join(words))).hexdigest()),
                  product=str(product), required_parity=True, control=False)
             for kind, reference in [('scalar', 'sleef_ln_scalar_fma'),
                                     ('latency', 'sleef_ln_scalar_fma'),
                                     ('vector', 'sleef_ln_avx512')]]
    manifest = dict(scope='Three-cell ln comparison; full #193 qualification remains separate',
                    source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                    builds=[dict(name='auto', sha256=digest(product))], cells=cells,
                    reference_sha256=digest(refs / 'libsleef.so.3'),
                    protocol=dict(upper95_t9=1.8331129326536335))
    (out / 'qualification-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(out)


if __name__ == '__main__':
    main()
