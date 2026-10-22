#!/usr/bin/env python3
"""Run the #152 reciprocal-pivot experiment; preserve every ABBA sample.

Uses summarize_tridiagonal_bench.py for per-cell summaries. Same-workload copy
controls additionally screen every Rust comparison. LAPACK retains its distinct
contract, RHS copy and Fortran interface. This is not a release qualification.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('rust', type=Path)
p.add_argument('lapack', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--cpu', type=int, required=True)
a = p.parse_args()
a.rust = a.rust.resolve()
a.lapack = a.lapack.resolve()
a.output.mkdir(parents=True, exist_ok=False)
os.sched_setaffinity(0, {a.cpu})
env = dict(os.environ)
env['LD_LIBRARY_PATH'] = str(a.lapack.parent / 'native-libs')


def read(path):
    try:
        return Path(path).read_text().strip()
    except OSError:
        return None


def command(*args):
    return subprocess.check_output(args, text=True).strip()


metadata = dict(cpu=a.cpu, started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                rust_sha256=hashlib.sha256(a.rust.read_bytes()).hexdigest(),
                lapack_sha256=hashlib.sha256(a.lapack.read_bytes()).hexdigest(),
                commit=command('git', 'rev-parse', 'HEAD'),
                rustc=command('rustc', '-Vv'), host=command('uname', '-a'),
                cpu_info=json.loads(command('lscpu', '-J')), features='simd,std',
                build='cargo build --locked --release -p morphiq-numerics-reference --all-features --bin bench-tridiagonal-reciprocal',
                rustflags=os.environ.get('RUSTFLAGS', ''),
                governor=read(f'/sys/devices/system/cpu/cpu{a.cpu}/cpufreq/scaling_governor'),
                turbo=read('/sys/devices/system/cpu/intel_pstate/no_turbo'),
                sibling_cpus=read(f'/sys/devices/system/cpu/cpu{a.cpu}/topology/thread_siblings_list'),
                load_start=read('/proc/loadavg'))
(a.output / 'metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')
(a.output / 'source.diff').write_text(command('git', 'diff', 'HEAD'))


def run(method, n, kind, rhs, calls):
    if method == 'lapack_solve':
        args = [str(a.lapack), str(n), kind, 'solve', 'fortran', str(calls), str(rhs)]
    else:
        args = [str(a.rust), str(n), kind, method, str(calls), str(rhs)]
    return int(subprocess.check_output(args, env=env, text=True))


cells = []
for n in [1, 17, 401, 4096]:
    for kind in ['ordinary', 'mixed', 'near']:
        cells.append((n, kind, 1, 'reciprocal_setup', 'division_setup'))
        for rhs in [1, 8, 64]:
            for first, second in [('reciprocal', 'division'),
                                  ('reciprocal_group', 'division_group'),
                                  ('reciprocal_certified', 'division_certified'),
                                  ('copy_control', 'division')]:
                cells.append((n, kind, rhs, first, second))
        if n > 1:
            cells.append((n, kind, 1, 'reciprocal', 'lapack_solve'))

with (a.output / 'raw.csv').open('w') as raw, (a.output / 'host.jsonl').open('w') as host:
    writer = csv.writer(raw)
    writer.writerow(['kind', 'n', 'rhs', 'pair', 'method', 'round', 'position', 'calls', 'elapsed_ns'])
    for cell_index, (n, kind, rhs, first, second) in enumerate(cells):
        counts = {method: max(1, 160_000_000 // max(1, run(method, n, kind, rhs, 16)))
                  for method in [first, second]}
        for method in [first, second, second, first]:
            run(method, n, kind, rhs, counts[method])
        for round_number in range(21):
            host.write(json.dumps(dict(cell=cell_index, round=round_number,
                       load=read('/proc/loadavg'),
                       frequency=read(f'/sys/devices/system/cpu/cpu{a.cpu}/cpufreq/scaling_cur_freq')))+'\n')
            for position, method in enumerate([first, second, second, first]):
                elapsed = run(method, n, kind, rhs, counts[method])
                writer.writerow([kind, n, rhs, first+':'+second, method, round_number, position,
                                 counts[method], elapsed])
            raw.flush()
        host.flush()
        print(f'{cell_index+1}/{len(cells)} n={n} {kind} rhs={rhs} {first}:{second}', flush=True)

summary = json.loads(command('python3', 'scripts/summarize_tridiagonal_bench.py', str(a.output/'raw.csv')))
controls = {(r['n'], r['kind'], r['rhs']): r for r in summary if r['pair'].startswith('copy_control:')}
for r in summary:
    control = controls[r['n'], r['kind'], r['rhs']]
    r['control_unstable'] = control['unstable']
    r['qualified_cell'] = not r['unstable'] and not r['control_unstable']
    r['gain_interval_below_one'] = r['ratio_interval'][1] < 1
(a.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
metadata.update(load_end=read('/proc/loadavg'),
                finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
(a.output/'metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')
