"""Stage a bounded fast-exp latency investigation using the shared paired runner.

All binaries must already exist. Run the staged run-qualification.py after builds
and oracle/proof work finish. No downloads, compilation, or retries during timing.
This focused native Linux investigation does not replace the full parity matrix.
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
for name in ['product', 'baseline', 'native', 'native-cache', 'core-math', 'sleef']:
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
         'references/libcoreexp.so': a.core_math, 'references/libsleef.so.3': a.sleef,
         'product.so': a.product, 'baseline.so': a.baseline}
pins = {}
for name, path in paths.items():
    shutil.copy2(path.resolve(), out/name)
    pins[name] = {'input': str(path.resolve()),
                  'sha256': hashlib.sha256((out/name).read_bytes()).hexdigest()}
# Exact deterministic inputs; discount and density cover S=100 BSM probes:
# rates/dividends times maturities, and -d^2/2 for |d| <= 8.
banks = {
    'ordinary': [-.2 + .4*i/51 for i in range(52)],
    'discount': [-4. + 4.4*i/51 for i in range(52)],
    'density': [-32.*i/51 for i in range(52)],
    'wide': [-703.999 + 1407.998*i/51 for i in range(52)],
    'mixed': [-704., 0., .1, -.1, 704., .2, -.2, -745.],
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
                           strong_fallbacks=sum(abs(x)>=704 for x in values))
    return entries[key]
cells = []
def add(kind, pop, n=52, ref='baseline', primitive='exp', control=False, required=False):
    ident = f'{primitive}-{kind}-{pop}-{n}-{ref}'
    cell = dict(id=ident, primitive=primitive, backend='auto', kind=kind,
                length=n, population=pop, reference=ref, control=control,
                required_parity=required, product=str(out/'product.so'), input=bank(pop,n))
    if ref == 'baseline':
        cell['reference_product'] = str(out/'baseline.so')
        if control:
            cell['control_product'] = str(out/'baseline.so')
    cells.append(cell)
for pop in ['ordinary', 'discount', 'density']:
    add('latency', pop, required=True)
    add('latency', pop, ref='glibc_exp')
for ref in ['core_math_exp', 'sleef_exp_scalar_fma']:
    add('latency', 'ordinary', ref=ref)
for ref in ['baseline', 'core_math_exp', 'sleef_exp_scalar_fma', 'glibc_exp']:
    add('scalar', 'ordinary', ref=ref)
for n in [1, 8, 52, 53, 4096]:
    add('vector', 'ordinary', n)
add('latency', 'wide')
add('vector', 'mixed', 53)
add('vector', 'ordinary', primitive='cdf')
for kind in ['latency', 'scalar']:
    add(kind, 'ordinary', control=True)
    cells[-1]['id'] += '-strong-control'
manifest = dict(cells=cells, builds=[dict(name='auto',sha256=pins['product.so']['sha256'],
                    control_sha256=pins['baseline.so']['sha256'])],
                protocol=dict(processes=10, blocks=2, paired_rounds_per_process=2,
                              target_ms=600, minimum_ms=250, upper95_t9=1.8331129326536335),
                interpretation='Required: dependent latency improves against baseline in all three ordinary/pricing input banks (upper one-sided 95% ratio <= 1). Throughput, wide, mixed, unchanged CDF and strong control are separate regression diagnostics; glibc/CORE-MATH/SLEEF are diagnostic comparators. Review every cell. Results apply only to the measured host and architecture; no consumer end-to-end qualification is implied.',
                source=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
                diff_sha256=hashlib.sha256(subprocess.check_output(['git','diff','HEAD'])).hexdigest(),
                binary_pins=pins)
(out/'qualification-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Staged {len(cells)} cells in {out}; run python3 {out}/run-qualification.py')
