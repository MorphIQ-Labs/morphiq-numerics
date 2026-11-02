"""Stage a focused fast normal CDF comparison of a candidate against a baseline.

Both C-ABI wrappers must already exist, built from `x86/matrix-wrapper` with the
same release profile and flags; performance is qualified on FMA builds
(AGENTS.md), so build both with `-C target-cpu=x86-64-v3` or a native FMA
target. Run the staged run-qualification.py after builds and oracle/proof work
finish. No downloads, compilation, or retries during timing. This focused native
Linux comparison does not replace the full parity matrix.
"""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import shutil
import struct
import subprocess

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', type=Path, required=True)
for name in ['product', 'baseline', 'native', 'native-cache', 'sleef']:
    parser.add_argument('--'+name, type=Path, required=True)
parser.add_argument('--cpu', type=int, required=True)
a = parser.parse_args()
if platform.system() != 'Linux' or platform.machine() not in ['x86_64', 'aarch64']:
    parser.error('Use native x86-64 or AArch64 Linux with glibc')
out = a.out.resolve()
out.mkdir(parents=True, exist_ok=False)
for name in ['qualify-cell.py', 'run-qualification.py']:
    shutil.copy2(HERE/name, out/name)
for name in ['protocol.py', 'inputs.py']:
    shutil.copy2(HERE.parent/name, out/name)
(out/'config.json').write_text(json.dumps({'cpu': a.cpu})+'\n')
for directory in ['bin', 'references', 'inputs']:
    (out/directory).mkdir()
paths = {'bin/native-matrix.so': a.native, 'bin/native-cache.so': a.native_cache,
         'references/libsleef.so.3': a.sleef, 'product.so': a.product, 'baseline.so': a.baseline}
pins = {}
for name, path in paths.items():
    shutil.copy2(path.resolve(), out/name)
    pins[name] = {'input': str(path.resolve()),
                  'sha256': hashlib.sha256((out/name).read_bytes()).hexdigest()}
# Exact deterministic banks inside the accelerated domain 2^-33 <= |x| <= 8.
# Pricing covers the d1/d2 range of ordinary contracts; body and the tails
# isolate each branch; mixed interleaves strong-owner fallbacks.
banks = {
    'pricing': [-4. + 8.*(i+.5)/52 for i in range(52)],
    'body': [-.66 + 1.32*(i+.5)/52 for i in range(52)],
    'lower': [-8. + 7.*(i+.5)/52 for i in range(52)],
    'upper': [1. + 7.*(i+.5)/52 for i in range(52)],
    'wide': [-8. + 16.*(i+.5)/52 for i in range(52)],
    'mixed': [-9., .3, -1.7, 9., 2.5, -4.2, float('inf'), -.05],
}
entries = {}
def bank(pop, n):
    key = f'{pop}-{n}'
    if key not in entries:
        values = [banks[pop][i % len(banks[pop])] for i in range(n)]
        words = [struct.pack('>d', x).hex() for x in values]
        path = out/'inputs'/(key+'.json')
        path.write_text(json.dumps(words)+'\n')
        entries[key] = dict(file=str(path), length=n,
                            sha256=hashlib.sha256(b''.join(bytes.fromhex(w) for w in words)).hexdigest(),
                            strong_fallbacks=sum(not 2.**-33 <= abs(x) <= 8 for x in values))
    return entries[key]
cells = []
def add(kind, pop, n=52, ref='baseline', control=False, required=True):
    ident = f'cdf-{kind}-{pop}-{n}-{ref}'
    cell = dict(id=ident, primitive='cdf', backend='auto', kind=kind,
                length=n, population=pop, reference=ref, control=control,
                required_parity=required, product=str(out/'product.so'), input=bank(pop, n))
    if ref == 'baseline':
        cell['reference_product'] = str(out/'baseline.so')
        if control:
            cell['control_product'] = str(out/'baseline.so')
    cells.append(cell)
for pop in ['pricing', 'body', 'lower', 'upper', 'wide']:
    add('latency', pop)
    add('scalar', pop)
    for n in [1, 2, 4, 8, 13, 52, 53, 4096]:
        add('vector', pop, n)
add('vector', 'mixed', 53, required=False)
add('vector', 'pricing', 4096, ref='sleef_cdf_avx512', required=False)
for kind in ['latency', 'scalar']:
    add(kind, 'pricing', control=True, required=False)
    cells[-1]['id'] += '-strong-control'
manifest = dict(cells=cells, builds=[dict(name='auto', sha256=pins['product.so']['sha256'],
                    control_sha256=pins['baseline.so']['sha256'])],
                protocol=dict(processes=10, blocks=2, paired_rounds_per_process=2,
                              target_ms=600, minimum_ms=250, upper95_t9=1.8331129326536335),
                interpretation='Required: in every accelerated-domain bank (pricing, body, lower and upper tails, wide), the candidate meets or beats the baseline in dependent latency, scalar throughput and every slice length (upper one-sided 95% ratio <= 1). Mixed fallback, SLEEF and the strong control are diagnostics. Results apply only to the measured host, architecture and build flags; no consumer end-to-end qualification is implied.',
                source=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                diff_sha256=hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD'])).hexdigest(),
                binary_pins=pins)
(out/'qualification-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(f'Staged {len(cells)} cells in {out}; run python3 {out}/run-qualification.py')
