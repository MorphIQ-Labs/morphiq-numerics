#!/usr/bin/env python3
"""Build and stage native far-tail CDF comparisons; never time during builds.

Uses the existing paired runner and timer. Baseline must precede the far-tail
change. The consumer composition is a weaker-contract diagnostic only.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import struct
import subprocess
import tomllib

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--baseline', required=True, type=Path)
    ap.add_argument('--cpu', type=int, default=2)
    ap.add_argument('--control-overhead-percent', type=float, default=0,
                    help='Owner-approved upper confidence budget for inputs outside the new far-tail domain')
    ap.add_argument('--x86-jcc-mitigation', action='store_true',
                    help='Separate diagnostic build: align branches on both products using LLVM JCC mitigation')
    args = ap.parse_args()
    if not math.isfinite(args.control_overhead_percent) or args.control_overhead_percent < 0:
        ap.error('Control overhead must be finite and nonnegative')
    toolchain = tomllib.loads((REPO/'rust-toolchain.toml').read_text())['toolchain']['channel']
    machine, system = platform.machine(), platform.system()
    mac = system == 'Darwin' and machine == 'arm64'
    if not mac and (system != 'Linux' or machine not in ('x86_64', 'aarch64')):
        ap.error('Native x86-64/AArch64 Linux or Apple Silicon required')
    if args.x86_jcc_mitigation and machine != 'x86_64':
        ap.error('--x86-jcc-mitigation requires x86-64')
    out = args.out.resolve()
    baseline = args.baseline.resolve()
    if subprocess.check_output(['git', '-C', str(baseline), 'status', '--porcelain']).strip():
        ap.error('Baseline checkout must be clean')
    out.mkdir(parents=True, exist_ok=False)
    for directory in ('bin', 'inputs', 'references'):
        (out / directory).mkdir()
    for name in ('qualify-cell.py', 'run-qualification.py', 'screen-ln.py'):
        shutil.copy2(HERE / 'x86' / name, out / name)
    for name in ('protocol.py', 'inputs.py'):
        shutil.copy2(HERE / name, out / name)
    for name in ('prepare-cdf-far.py', 'observe-cdf-far.py'):
        shutil.copy2(HERE / name, out / name)
    (out / 'config.json').write_text(json.dumps({'cpu': args.cpu}) + '\n')
    commands = []

    def run(command, **kwargs):
        commands.append(command)
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        subprocess.run(command, check=True, **kwargs)

    link = '-dynamiclib' if mac else '-shared'
    for timer in ('native-matrix', 'native-cache'):
        run(['cc', '-O3', '-fPIC', link, '-ffp-contract=off', '-DNO_SLEEF',
             str(HERE / 'x86' / (timer + '.c')), '-o', str(out / 'bin' / (timer + '.so'))])
    variants = [('auto', 'simd,std', '-C target-cpu=x86-64-v3' if machine == 'x86_64' else '')]
    if machine == 'x86_64':
        variants += [('avx2', 'simd', '-C target-cpu=x86-64-v3'),
                     ('avx512', 'simd', '-C target-cpu=x86-64-v4')]
    if args.x86_jcc_mitigation:
        variants = [(name, features, flags + ' -C llvm-args=--x86-branches-within-32B-boundaries')
                    for name, features, flags in variants]
    builds, cells, entries, pins = [], [], {}, {}
    wrapper = (HERE / 'x86/matrix-wrapper/src/lib.rs').read_text()
    composition = '''
fn composition(x: f64) -> f64 {
    let a = x.abs();
    let scaled = a * core::f64::consts::FRAC_1_SQRT_2;
    if a <= 8.0 || scaled >= 16.0 {
        return morphiq_numerics::fast::normal::norm_cdf(x);
    }
    let lower = 0.5 * morphiq_numerics::fast::elementary::exp(-0.5*a*a)
        * morphiq_numerics::fast::normal::erfcx(scaled);
    if x < 0.0 { lower } else { 1.0 - lower }
}
'''
    # The diagnostic composition uses the old entry outside its composition row.
    comp_wrapper = wrapper.replace('morphiq_numerics::fast::normal::norm_cdf(x)', 'composition(x)')
    comp_wrapper = comp_wrapper.replace(
        'morphiq_numerics::fast::normal::norm_cdf_slice(std::slice::from_raw_parts(x,n),std::slice::from_raw_parts_mut(y,n));',
        'for i in 0..n { *y.add(i) = composition(*x.add(i)); }') + composition
    for backend, features, flags in variants:
        products = {}
        for role, source, code in [('candidate', REPO, wrapper), ('baseline', baseline, wrapper),
                                   ('composition', baseline, comp_wrapper)]:
            folder = out / (backend + '-' + role)
            (folder / 'src').mkdir(parents=True)
            (folder / 'src/lib.rs').write_text(code)
            (folder / 'Cargo.toml').write_text(f'''[package]
name="cdf-far-wrapper"
version="0.0.0"
edition="2024"
[workspace]
[lib]
crate-type=["cdylib"]
[dependencies]
morphiq-numerics={{path={json.dumps(str(source / 'crates/morphiq-numerics'))},default-features=false,features={json.dumps(features.split(','))}}}
[profile.release]
lto="thin"
codegen-units=1
''')
            env = dict(os.environ)
            for key in ('CARGO_ENCODED_RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
                        'CARGO_BUILD_TARGET', 'CARGO_BUILD_RUSTFLAGS'):
                env.pop(key, None)
            # Reuse build output; retain the exact linked products separately.
            env.update(RUSTFLAGS=flags, CARGO_TARGET_DIR=str(out / 'build'), RUSTUP_TOOLCHAIN=toolchain)
            run(['cargo', 'build', '--release', '--manifest-path', str(folder / 'Cargo.toml')], env=env)
            product = out / 'bin' / f'{backend}-{role}.so'
            shutil.copy2(out / 'build/release' / ('libcdf_far_wrapper.dylib' if mac else 'libcdf_far_wrapper.so'), product)
            products[role] = str(product)
            pins[str(product)] = sha(product)
        builds.append(dict(name=backend, features=features, rustflags=flags,
                           sha256=pins[products['candidate']], control_sha256=pins[products['baseline']]))
        # Preserve the exploratory timer's exact xorshift bank construction.
        def far(hi, signs):
            word, values = 0x9e3779b97f4a7c15, []
            for i in range(4096):
                word ^= (word << 13) & ((1 << 64)-1)
                word ^= word >> 7
                word ^= (word << 17) & ((1 << 64)-1)
                x = 8.0 + (hi-8.0) * ((word >> 11) / float(1 << 53))
                values.append(-x if signs == 'negative' or signs == 'mixed' and i % 2 == 0 else x)
            return values
        # Existing generated normal threshold; its neighbour bracket is proved
        # in NormalTailThresholdConstants.normal_cdf_one_tail_bracket.
        cdf_one = struct.unpack('>d', bytes.fromhex('402095b059d67c4d'))[0]
        banks = {'far_negative': far(22.5, 'negative'), 'far_mixed': far(22.5, 'mixed'),
                 'far_mixed16': far(16.0, 'mixed'), 'positive_fallback': far(22.5, 'positive'),
                 'pricing': [-4.+8.*(i+.5)/52 for i in range(52)],
                 'body': [-.66+1.32*(i+.5)/52 for i in range(52)],
                 'lower': [-8.+7.*(i+.5)/52 for i in range(52)],
                 'upper': [1.+7.*(i+.5)/52 for i in range(52)],
                 'wide': [-8.+16.*(i+.5)/52 for i in range(52)],
                 'seams': [math.nextafter(x, direction) for x in (-22.5, -8., 8., cdf_one, 22.5)
                           for direction in (-math.inf, x, math.inf)],
                 'mixed': [-30., -.3, -10., 9., -22., -4.2, -38., 0., -8., -22.5],
                 'fallback': [-40., -30., 0., 2.**-40, 9., 30.]}

        def add(pop, kind, n, ref='baseline', control=False):
            key = f'{pop}-{n}'
            if key not in entries:
                values = [banks[pop][i % len(banks[pop])] for i in range(n)]
                words = [struct.pack('>d', x).hex() for x in values]
                path = out / 'inputs' / (key + '.json')
                path.write_text(json.dumps(words) + '\n')
                entries[key] = dict(file=str(path), length=n,
                    sha256=hashlib.sha256(b''.join(bytes.fromhex(w) for w in words)).hexdigest(),
                    baseline_fallbacks=sum(not 2.**-33 <= abs(x) <= 8 for x in values),
                    candidate_fallbacks=sum(not (2.**-33 <= abs(x) <= 8 or -22.5 <= x < -8 or x >= cdf_one) for x in values),
                    candidate_exact_endpoints=sum(x >= cdf_one for x in values))
            cell = dict(id=f'{backend}-{pop}-{kind}-{n}-{ref}' + ('-strong' if control else ''),
                primitive='cdf', backend=backend, kind=kind, length=n, population=pop,
                reference=ref, control=control, required_parity=ref == 'baseline' and not control,
                product=products['candidate'], reference_product=products[ref], input=entries[key])
            unchanged = not any(-22.5 <= x < -8 for x in
                                (banks[pop][i % len(banks[pop])] for i in range(n)))
            cell['unchanged_domain'] = unchanged
            cell['max_time_ratio'] = (1+args.control_overhead_percent/100
                                      if unchanged and ref == 'baseline' else 1)
            cell['balanced_stack'] = machine == 'x86_64' and kind != 'latency'
            if control:
                cell['control_product'] = products['baseline']
            cells.append(cell)
        # Priority screen covers the new row and unchanged hot domains first.
        for pop in ('far_negative', 'pricing', 'lower', 'body', 'positive_fallback', 'far_mixed', 'far_mixed16'):
            for kind, n in [('scalar', 52), ('latency', 52), ('vector', 4096)]:
                add(pop, kind, n)
        for pop in banks:
            for kind, n in [('scalar', 52), ('latency', 52)] + [('vector', n) for n in (1, 2, 4, 8, 13, 52, 53, 4096)]:
                if not any(c['backend'] == backend and c['population'] == pop and c['kind'] == kind and c['length'] == n for c in cells):
                    add(pop, kind, n)
        for pop in ('far_negative', 'far_mixed', 'far_mixed16'):
            for kind, n in [('scalar', 52), ('latency', 52), ('vector', 4096)]:
                add(pop, kind, n, ref='composition')
        for kind, n in [('scalar', 52), ('latency', 52), ('vector', 4096)]:
            add('pricing', kind, n, control=True)
    # Screen all backends' priority cells before the remaining lengths/banks.
    cells.sort(key=lambda c: (not (c['population'] in ('far_negative', 'pricing', 'lower', 'body', 'positive_fallback', 'far_mixed', 'far_mixed16') and
                                  (c['kind'] != 'vector' or c['length'] == 4096) and c['required_parity']),
                              next(i for i,b in enumerate(builds) if b['name'] == c['backend'])))
    # Complete the observed regression-sensitive controls first, retaining
    # every declared cell and the same per-cell confidence/stop rule.
    priority = {('positive_fallback', 'scalar', 52),
                ('positive_fallback', 'latency', 52),
                ('positive_fallback', 'vector', 4096),
                ('pricing', 'scalar', 52), ('pricing', 'vector', 8),
                ('body', 'scalar', 52), ('lower', 'latency', 52)}
    first = [c['id'] for c in cells if c['required_parity'] and
             (c['population'], c['kind'], c['length']) in priority]
    first_ids = set(first)
    groups = [first, [c['id'] for c in cells if c['id'] not in first_ids]]
    source_paths = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard'], text=True).splitlines()
    source_files = {name: sha(REPO / name) for name in source_paths
        if (REPO / name).is_file() and (
            name.startswith(('crates/morphiq-numerics/', 'crates/morphiq-numerics-arch/',
                             'scripts/bench_fast/')) or
            name in ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml'))}
    manifest = dict(cells=cells, builds=builds, binary_pins=pins, source_files=source_files,
        source=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        source_diff_sha256=hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD'])).hexdigest(),
        baseline=subprocess.check_output(['git', '-C', str(baseline), 'rev-parse', 'HEAD'], text=True).strip(),
        protocol=dict(processes=10, blocks=2, paired_rounds_per_process=2,
                      target_ms=600, minimum_ms=250, upper95_t9=1.8331129326536335),
        stop_on_required_failure=True, execution_groups=groups,
        toolchain=toolchain, control_overhead_percent=args.control_overhead_percent,
        interpretation='Every required cell must meet its declared max_time_ratio at upper one-sided 95% confidence. No aggregation across cells. Independent x86 throughput averages all 256 ABI-aligned stack positions, interleaving paired chunks. Latency retains uninterrupted chains. Composition and unchanged strong controls reviewed separately; the composition cost/spread criterion is not waived by diagnostic classification. Native host only; not consumer end-to-end or the historical full competitor matrix.')
    (out / 'qualification-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    (out / 'host.json').write_text(json.dumps(dict(platform=platform.platform(), machine=machine,
        rustc=subprocess.check_output(['rustc', '+'+toolchain, '-Vv'], text=True),
        cc=subprocess.check_output(['cc', '--version'], text=True)), indent=2) + '\n')
    print(f'Staged {len(cells)} cells. Run observations before screen-ln.py or qualification.')


if __name__ == '__main__':
    main()
