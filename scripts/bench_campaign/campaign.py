#!/usr/bin/env python3
"""Run the established native comparison matrix with source and comparison receipts."""
import argparse
import datetime as dt
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[2]
NATIVE = REPO / 'scripts/bench_fast'
PINS = {
    'core-math': 'c7100a07428584639defdd64409e3621884c362b',
    'sleef': '906ca7512ee483296780a81a21b9ca715d40dfe1',
    'libcerf': '7e6b637031b5c6cbc89a5f7220bf4ef07518d035',
}
PACKAGES = {'scipy': '1.16.3', 'numpy': '2.3.4', 'mpmath': '1.3.0'}
LIBRARIES = {
    'x86-linux': {'core-math': ['libcoreexp.so'], 'sleef': ['libsleef.so', 'libsleef.so.3'], 'libcerf': ['libcerf.so']},
    'arm-macos': {'core-math': ['libcoreexp.dylib'], 'sleef': ['libsleef.3.dylib', 'libsleef.3.9.0.dylib'], 'libcerf': ['libcerf.3.1.dylib']},
}


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.new')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')
    temporary.replace(path)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def stamp():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def git_revision(path):
    def git(*args):
        return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()
    if git('status', '--porcelain'):
        raise ValueError(f'Checkout must be clean: {path}')
    return git('rev-parse', 'HEAD')


def package_receipt():
    """Hash installed black-box tools without inspecting their implementation."""
    result = {}
    for name, version in PACKAGES.items():
        dist = importlib.metadata.distribution(name)
        if dist.version != version:
            raise ValueError(f'{name}: expected {version}, found {dist.version}')
        files = {}
        for entry in dist.files or []:
            path = Path(dist.locate_file(entry)).absolute()
            if path.is_file() and path.suffix != '.pyc':
                files[str(path)] = sha(path)
        if not files:
            raise ValueError(f'No installed distribution files for {name}')
        result[name] = {'version': version, 'files': files}
    return result


def verify_files(files):
    for name, expected in files.items():
        if sha(name) != expected:
            raise ValueError(f'Frozen file changed: {name}')


def reference_lock(args):
    """Record reviewed reference builds, their source pins and build commands."""
    catalogue = read(Path(__file__).with_name('references.json'))
    records = {}
    for name, pin in PINS.items():
        source = getattr(args, name.replace('-', '_') + '_source').resolve()
        if git_revision(source) != pin:
            raise ValueError(f'{name}: checkout must be at {pin}')
        records[name] = {
            **catalogue[name], 'revision': pin, 'source': str(source),
            'files': {str((args.reference_bin.resolve() / n).absolute()): sha(args.reference_bin / n)
                      for n in LIBRARIES[args.platform][name]},
        }
    build_log = args.build_log.resolve()
    if not build_log.read_text().strip():
        raise ValueError('Reference build command log must not be empty')
    lock = {'schema': 1, 'platform': args.platform, 'references': records,
            'packages': package_receipt(), 'scipy_contract': catalogue['scipy'], 'build_log': {'path': str(build_log), 'sha256': sha(build_log)}}
    # Refuse to replace a lock used by an earlier attempt.
    with args.out.open('x') as stream:
        json.dump(lock, stream, indent=2)
        stream.write('\n')


def validate_lock(lock, kind, reference_bin):
    if lock['schema'] != 1 or lock['platform'] != kind or set(lock['references']) != set(PINS):
        raise ValueError('Reference lock must cover all canonical native references for this platform')
    catalogue = read(Path(__file__).with_name('references.json'))
    if lock['scipy_contract'] != catalogue['scipy']:
        raise ValueError('SciPy reference contract differs from catalogue')
    for name, pin in PINS.items():
        record = lock['references'][name]
        if record['revision'] != pin or any(record.get(k) != v for k, v in catalogue[name].items()):
            raise ValueError(f'{name}: reference identity or contract differs from the reviewed catalogue')
        expected_paths = {str((reference_bin / n).absolute()) for n in LIBRARIES[kind][name]}
        if set(record['files']) != expected_paths:
            raise ValueError(f'{name}: locked binaries do not match --reference-bin')
        verify_files(record['files'])
    verify_files({lock['build_log']['path']: lock['build_log']['sha256']})
    if lock['packages'] != package_receipt():
        raise ValueError('Installed oracle/reference packages differ from reference lock')


def host_snapshot():
    commands = [['uname', '-a'], ['rustc', '-Vv'], ['cc', '--version'], ['cmake', '--version']]
    if platform.system() == 'Linux':
        commands += [['lscpu', '-J'], ['ps', '-eo', 'pid,pcpu,comm']]
    else:
        commands += [['sysctl', '-a'], ['pmset', '-g', 'therm'], ['pmset', '-g', 'batt']]
    records = []
    for command in commands:
        try:
            result = subprocess.run(command, text=True, capture_output=True, timeout=10)
            records.append({'argv': command, 'code': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr})
        except (OSError, subprocess.TimeoutExpired) as exc:
            records.append({'argv': command, 'error': str(exc)})
    return {'utc': stamp(), 'system': platform.system(), 'machine': platform.machine(),
            'python': sys.version, 'executable': sys.executable, 'commands': records,
            'affinity': sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else None}


def run_stage(argv, cwd, log, deadline):
    """A stage owns its process group, including benchmark grandchildren."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError('Campaign deadline reached')
    with log.open('x') as stream:
        process = subprocess.Popen(argv, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            return process.wait(timeout=remaining)
        finally:
            # A stage must not leave background children using the benchmark host.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()


def comparison_rows(native, kind):
    """Keep the native decision; never re-estimate statistics in the controller."""
    if kind == 'x86-linux':
        cells = read(native / 'qualification-manifest.json')['cells']
        path = native / 'qualification/summary.json'
        summary = read(path) if path.exists() else []
        measured = {r['id']: r for r in summary}
        rows = []
        for cell in cells:
            row = measured.get(cell['id'])
            rows.append({'cell': cell, 'measurement': row,
                         'passed': bool(row and row['passes'] and row['valid_duration'])})
    else:
        cells = read(native / 'cells.json')
        path = native / 'qualification-summary.json'
        summary = read(path)['cells'] if path.exists() else []
        measured = {r['id']: r for r in summary}
        rows = [{'cell': c, 'measurement': measured.get(c['id']),
                 'passed': bool(measured.get(c['id'], {}).get('meets_cost') and
                                measured.get(c['id'], {}).get('duration_pass'))} for c in cells]
    ids = [c['id'] for c in cells]
    if len(set(ids)) != len(ids) or len(measured) != len(summary) or not set(measured).issubset(ids):
        raise ValueError('Duplicate or unexpected comparison cells')
    required_key = 'required_parity' if kind == 'x86-linux' else 'parity_required'
    references = {c['reference'] if kind == 'x86-linux' else c['pair'][1] for c in cells}
    if not {'core_math_exp', 'libcerf_erfcx', 'scipy_ndtr'}.issubset(references) or not any(r.startswith('sleef_') for r in references):
        raise ValueError('Matrix must include CORE-MATH, SLEEF, libcerf and SciPy comparisons')
    for reference in references:
        if reference not in {'core_math_exp', 'libcerf_erfcx', 'scipy_ndtr', 'strong-control'} and not reference.startswith('sleef_'):
            raise ValueError(f'Undocumented comparator: {reference}')
    if not cells or not any(c[required_key] for c in cells):
        raise ValueError('Empty qualification matrix')
    for row in rows:
        reference = row['cell']['reference'] if kind == 'x86-linux' else row['cell']['pair'][1]
        row['reference'] = reference
        row['comparison_kind'] = 'baseline-control' if reference == 'strong-control' else 'canonical'
        row['candidate_contract'] = 'strong' if row['comparison_kind'] == 'baseline-control' else 'fast'
        row['required'] = row['cell'][required_key]
    return {'complete': len(measured) == len(cells), 'cells': rows,
            'missing': [r['cell']['id'] for r in rows if r['measurement'] is None],
            'required_failed': [r['cell']['id'] for r in rows if r['required'] and not r['passed']]}


def check_x86_host(cpu):
    if cpu not in os.sched_getaffinity(0):
        raise ValueError('Selected CPU is outside the allowed affinity set')
    processors = [dict(line.split(':', 1) for line in block.splitlines() if ':' in line)
                  for block in Path('/proc/cpuinfo').read_text().strip().split('\n\n')]
    records = [{key.strip(): value.strip() for key, value in record.items()} for record in processors]
    selected = next((record for record in records if record.get('processor') == str(cpu)), {})
    flags = selected.get('flags', '').split()
    if not {'sse2', 'avx2', 'fma', 'avx512f'}.issubset(flags):
        raise ValueError('The full x86 matrix requires SSE2, AVX2/FMA and AVX-512F')


def execute(args):
    kind = args.platform
    native_platform = ('Linux', 'x86_64') if kind == 'x86-linux' else ('Darwin', 'arm64')
    if (platform.system(), platform.machine()) != native_platform:
        raise ValueError(f'{kind} requires a native {native_platform} host')
    if not math.isfinite(args.timeout_hours) or args.timeout_hours <= 0:
        raise ValueError('Timeout must be finite and positive')
    revision = git_revision(REPO)
    if revision != args.commit:
        raise ValueError(f'Candidate checkout is {revision}, expected {args.commit}')
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
        raise ValueError('Native assertion checks require Python optimization disabled')
    if kind == 'x86-linux':
        if not args.control_source or not args.control_commit:
            raise ValueError('x86 requires --control-source and --control-commit')
        if git_revision(args.control_source) != args.control_commit:
            raise ValueError('Baseline checkout does not match --control-commit')
        check_x86_host(args.cpu)
    elif not args.sleef_include:
        raise ValueError('macOS ARM requires --sleef-include')
    notes = args.host_notes.read_text()
    if not notes.strip():
        raise ValueError('Record power/thermal conditions, SMT sibling, contention and unavailable telemetry')
    lock = read(args.reference_lock)
    reference_bin = args.reference_bin.resolve()
    validate_lock(lock, kind, reference_bin)
    out = args.out.resolve()
    out.relative_to(REPO / 'target')
    out.mkdir(parents=True, exist_ok=False)
    native = out / 'native'
    deadline = time.monotonic() + args.timeout_hours * 3600
    receipt = {'schema': 1, 'started': stamp(), 'state': 'running', 'candidate': revision,
               'control': args.control_commit, 'platform': kind, 'cpu': args.cpu,
               'timeout_hours': args.timeout_hours, 'host_notes': notes, 'reference_lock': lock,
               'qualification_passed': False, 'stages': [], 'host_before': host_snapshot()}
    write(out / 'campaign.json', receipt)
    (out / 'reference-build.log').write_bytes(Path(lock['build_log']['path']).read_bytes())
    prepare = [sys.executable, str(NATIVE / 'prepare.py'), '--platform', kind, '--out', str(native),
               '--reference-bin', str(reference_bin), '--cpu', str(args.cpu)]
    if kind == 'x86-linux':
        prepare += ['--control-source', str(args.control_source.resolve())]
    else:
        prepare += ['--sleef-include', str(args.sleef_include.resolve())]
    stages = [('prepare', prepare), ('observe', [sys.executable, str(native / 'observe.py')])]
    if kind == 'arm-macos':
        stages += [('observe-references', [sys.executable, str(native / 'observe-references.py')]),
                   ('diagnostics', [sys.executable, str(native / 'diagnostics.py')])]
    stages += [('freeze', [sys.executable, str(NATIVE / 'freeze.py'), str(native)]),
               ('measure', [sys.executable, str(native / ('run-qualification.py' if kind == 'x86-linux' else 'run-qualified.py'))])]
    try:
        for name, argv in stages:
            entry = {'stage': name, 'argv': argv, 'started': stamp()}
            receipt['stages'].append(entry)
            write(out / 'campaign.json', receipt)
            if name == 'measure':
                if git_revision(REPO) != revision:
                    raise ValueError('Candidate changed during preparation')
                if kind == 'x86-linux' and git_revision(args.control_source) != args.control_commit:
                    raise ValueError('Baseline changed during preparation')
                validate_lock(lock, kind, reference_bin)
                verify_files(read(native / 'source.json')['files'])
            code = run_stage(argv, REPO, out / (name + '.log'), deadline)
            entry.update(finished=stamp(), exit_code=code)
            if name == 'prepare' and not code:
                comparison_rows(native, kind)  # Check canonical coverage before spending timing time.
            if code:
                raise RuntimeError(f'{name} failed ({code}); see {out / (name + ".log")}')
        receipt['state'] = 'executed'
    except (Exception, KeyboardInterrupt) as exc:
        receipt.update(state='failed', error=f'{type(exc).__name__}: {exc}')
    finally:
        try:
            if (native / 'source.json').exists():
                verify_files(read(native / 'source.json')['files'])
                validate_lock(lock, kind, reference_bin)
                receipt['frozen_files_verified'] = True
            else:
                receipt['frozen_files_verified'] = False
            if (native / ('qualification-manifest.json' if kind == 'x86-linux' else 'cells.json')).exists():
                comparison = comparison_rows(native, kind)
                write(out / 'comparisons.json', comparison)
                receipt['qualification_passed'] = bool(receipt['state'] == 'executed' and
                    receipt['frozen_files_verified'] and comparison['complete'] and not comparison['required_failed'])
        except Exception as exc:
            receipt.update(state='failed', verification_error=f'{type(exc).__name__}: {exc}', qualification_passed=False)
        receipt.update(finished=stamp(), host_after=host_snapshot())
        write(out / 'campaign.json', receipt)
        # Index artifacts on both success and failure, without deleting failed attempts.
        write(out / 'artifacts.json', {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                                     if p.is_file() and p.name != 'artifacts.json' and '__pycache__' not in p.parts})
    return 0 if receipt.get('qualification_passed') else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    lock = sub.add_parser('lock-references')
    lock.add_argument('--platform', choices=LIBRARIES, required=True)
    lock.add_argument('--reference-bin', type=Path, required=True)
    for name in PINS:
        lock.add_argument('--' + name + '-source', type=Path, required=True)
    lock.add_argument('--build-log', type=Path, required=True)
    lock.add_argument('--out', type=Path, required=True)
    run = sub.add_parser('run')
    run.add_argument('--platform', choices=LIBRARIES, required=True)
    run.add_argument('--commit', required=True)
    run.add_argument('--control-source', type=Path)
    run.add_argument('--control-commit')
    run.add_argument('--reference-bin', type=Path, required=True)
    run.add_argument('--reference-lock', type=Path, required=True)
    run.add_argument('--sleef-include', type=Path)
    run.add_argument('--cpu', type=int, default=2)
    run.add_argument('--host-notes', type=Path, required=True)
    run.add_argument('--timeout-hours', type=float, required=True)
    run.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == 'lock-references':
            reference_lock(args)
            return 0
        # SIGTERM follows the same evidence and child cleanup path as Ctrl-C.
        def interrupted(signum, frame):
            raise KeyboardInterrupt(f'signal {signum}')
        signal.signal(signal.SIGTERM, interrupted)
        return execute(args)
    except (ValueError, OSError, KeyError, importlib.metadata.PackageNotFoundError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    sys.exit(main())
