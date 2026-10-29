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
import shutil
import subprocess
import sys
import time

if __package__:
    from . import selection
else:
    import selection

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
    full = read(native / 'matrix-full.json')['cells'] if (native / 'matrix-full.json').exists() else cells
    plan = read(native / 'selection.json') if (native / 'selection.json').exists() else None
    if plan and cells != selection.selected_cells(full, plan):
        raise ValueError('Active cells differ from the declared selection')
    selection.validate_full(full, kind)
    ids = [c['id'] for c in cells]
    if len(set(ids)) != len(ids) or len(measured) != len(summary) or not set(measured).issubset(ids):
        raise ValueError('Duplicate or unexpected comparison cells')
    required_key = 'required_parity' if kind == 'x86-linux' else 'parity_required'
    for row in rows:
        reference = row['cell']['reference'] if kind == 'x86-linux' else row['cell']['pair'][1]
        row['reference'] = reference
        row['comparison_kind'] = 'baseline-control' if reference == 'strong-control' else 'canonical'
        row['candidate_contract'] = 'strong' if row['comparison_kind'] == 'baseline-control' else 'fast'
        row['required'] = row['cell'][required_key]
    return {'complete': len(measured) == len(cells), 'cells': rows,
            'suite': plan['suite'] if plan else 'full',
            'full_cell_count': len(full), 'selected_cell_count': len(cells),
            'excluded': plan['excluded_ids'] if plan else [],
            'missing': [r['cell']['id'] for r in rows if r['measurement'] is None],
            'required_failed': [r['cell']['id'] for r in rows if r['required'] and not r['passed']]}


def matrix(native, kind):
    return read(native / 'qualification-manifest.json') if kind == 'x86-linux' else {'cells': read(native / 'cells.json'), 'groups': read(native / 'groups.json')}


def apply_selection(native, kind, args):
    full = matrix(native, kind)
    plan = selection.select(full['cells'], kind, args.suite, args.primitive, args.backend, args.cell)
    selected = selection.selected_cells(full['cells'], plan)
    write(native / 'matrix-full.json', full)
    write(native / 'selection.json', plan)
    if kind == 'x86-linux':
        write(native / 'qualification-manifest.json', {**full, 'cells': selected})
    else:
        write(native / 'cells.json', selected)
        groups = {name: [i for i in ids if i in plan['selected_ids']] for name, ids in full['groups'].items()}
        groups = {name: ids for name, ids in groups.items() if ids}
        grouped = [i for ids in groups.values() for i in ids]
        if sorted(grouped) != sorted(plan['selected_ids']):
            raise ValueError('ARM groups must cover every selected cell exactly once')
        write(native / 'groups.json', groups)
    return plan


def prepared_configuration(args):
    return {key: str(getattr(args, key).resolve()) if isinstance(getattr(args, key), Path) else getattr(args, key)
            for key in ['platform', 'commit', 'control_source', 'control_commit', 'reference_bin',
                        'reference_lock', 'sleef_include', 'cpu']}


def verify_prepared(native):
    outputs = ['qualification', 'qualified', 'qualification-observations', 'logs', 'host',
               'qualification-summary.json', 'COMPLETE', 'selection.json', 'matrix-full.json']
    if any((native / name).exists() for name in outputs):
        raise ValueError('Bootstrap contains prior observations or measurements; create a fresh bootstrap')
    verify_files(read(native / 'source.json')['files'])


def load_prepared(args):
    receipt = read(args.prepared / 'campaign.json')
    if receipt['state'] != 'prepared' or not receipt['frozen_files_verified']:
        raise ValueError('--prepared must name a successful bootstrap, not a previous timing attempt')
    for key, value in receipt['configuration'].items():
        current = getattr(args, key)
        normalized = str(current.resolve()) if isinstance(current, Path) else current
        if current is not None and normalized != value:
            raise ValueError(f'Prepared {key} differs from the requested configuration')
        setattr(args, key, Path(value) if key in ['control_source', 'reference_bin', 'reference_lock', 'sleef_include'] and value else value)
    verify_prepared(args.prepared / 'native')
    return receipt


def copy_prepared(source, destination, kind):
    # Copy, never hard-link writable manifests. Retain the bootstrap because
    # native loader paths may still name its build outputs (notably on macOS).
    shutil.copytree(source, destination, symlinks=True, ignore=shutil.ignore_patterns('__pycache__'))
    (destination / 'source.json').unlink()
    if kind == 'x86-linux':
        full = read(destination / 'qualification-manifest.json')
        for cell in full['cells']:
            cell['product'] = str(destination / Path(cell['product']).relative_to(source))
            cell['input']['file'] = str(destination / Path(cell['input']['file']).relative_to(source))
        write(destination / 'qualification-manifest.json', full)


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
    if args.prepared:
        args.prepared = args.prepared.resolve()
        load_prepared(args)
    if not all([args.platform, args.commit, args.reference_bin, args.reference_lock]):
        raise ValueError('Supply --prepared or --platform, --commit, --reference-bin and --reference-lock')
    if args.cpu is None:
        args.cpu = 2
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
               'qualification_passed': False, 'selected_passed': False, 'configuration': prepared_configuration(args),
               'prepared_from': str(args.prepared) if args.prepared else None, 'stages': [], 'host_before': host_snapshot()}
    write(out / 'campaign.json', receipt)
    (out / 'reference-build.log').write_bytes(Path(lock['build_log']['path']).read_bytes())
    prepare = [sys.executable, str(NATIVE / 'prepare.py'), '--platform', kind, '--out', str(native),
               '--reference-bin', str(reference_bin), '--cpu', str(args.cpu)]
    if kind == 'x86-linux':
        prepare += ['--control-source', str(args.control_source.resolve())]
    else:
        prepare += ['--sleef-include', str(args.sleef_include.resolve())]
    stages = [('reuse-prepared' if args.prepared else 'prepare', None if args.prepared else prepare), ('observe', [sys.executable, str(native / 'observe.py')])]
    if kind == 'arm-macos':
        stages += [('observe-references', [sys.executable, str(native / 'observe-references.py')]),
                   ('diagnostics', [sys.executable, str(native / 'diagnostics.py')])]
    stages += [('freeze', [sys.executable, str(NATIVE / 'freeze.py'), str(native)]),
               ('measure', [sys.executable, str(native / ('run-qualification.py' if kind == 'x86-linux' else 'run-qualified.py'))])]
    if args.command == 'bootstrap':
        stages = [('prepare', prepare), ('freeze', [sys.executable, str(NATIVE / 'freeze.py'), str(native)])]
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
                if args.prepared:
                    verify_prepared(args.prepared / 'native')
            if name == 'reuse-prepared':
                copy_prepared(args.prepared / 'native', native, kind)
                code = 0
            else:
                code = run_stage(argv, REPO, out / (name + '.log'), deadline)
            entry.update(finished=stamp(), exit_code=code)
            if name in ['prepare', 'reuse-prepared'] and not code:
                selection.validate_full(matrix(native, kind)['cells'], kind)
                if args.command != 'bootstrap':
                    receipt['selection'] = apply_selection(native, kind, args)
            if code:
                raise RuntimeError(f'{name} failed ({code}); see {out / (name + ".log")}')
        receipt['state'] = 'prepared' if args.command == 'bootstrap' else 'executed'
    except (Exception, KeyboardInterrupt) as exc:
        receipt.update(state='failed', error=f'{type(exc).__name__}: {exc}')
    finally:
        try:
            if (native / 'source.json').exists():
                verify_files(read(native / 'source.json')['files'])
                validate_lock(lock, kind, reference_bin)
                if args.prepared:
                    verify_prepared(args.prepared / 'native')
                receipt['frozen_files_verified'] = True
            else:
                receipt['frozen_files_verified'] = False
            if (native / ('qualification-manifest.json' if kind == 'x86-linux' else 'cells.json')).exists():
                comparison = comparison_rows(native, kind)
                write(out / 'comparisons.json', comparison)
                receipt['selected_passed'] = bool(receipt['state'] == 'executed' and
                    receipt['frozen_files_verified'] and comparison['complete'] and not comparison['required_failed'])
                receipt['qualification_passed'] = receipt['selected_passed'] and comparison['suite'] == 'full'
        except Exception as exc:
            receipt.update(state='failed', verification_error=f'{type(exc).__name__}: {exc}', qualification_passed=False, selected_passed=False)
        receipt.update(finished=stamp(), host_after=host_snapshot())
        write(out / 'campaign.json', receipt)
        # Index artifacts on both success and failure, without deleting failed attempts.
        write(out / 'artifacts.json', {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                                     if p.is_file() and p.name != 'artifacts.json' and '__pycache__' not in p.parts})
    return 0 if receipt['state'] == 'prepared' or (receipt['state'] == 'executed' and receipt['selected_passed']) else 1


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
    for name in ['bootstrap', 'run']:
        run = sub.add_parser(name)
        run.add_argument('--platform', choices=LIBRARIES)
        run.add_argument('--commit')
        run.add_argument('--control-source', type=Path)
        run.add_argument('--control-commit')
        run.add_argument('--reference-bin', type=Path)
        run.add_argument('--reference-lock', type=Path)
        run.add_argument('--sleef-include', type=Path)
        run.add_argument('--cpu', type=int)
        run.add_argument('--host-notes', type=Path, required=True)
        run.add_argument('--timeout-hours', type=float, required=True)
        run.add_argument('--out', type=Path, required=True)
        if name == 'run':
            run.add_argument('--prepared', type=Path)
            run.add_argument('--suite', choices=['full', 'smoke', 'subset'], default='full')
            run.add_argument('--primitive', action='append', default=[], choices=['exp', 'erfcx', 'cdf'])
            run.add_argument('--backend', action='append', default=[], choices=['auto', 'sse2', 'avx2', 'avx512'])
            run.add_argument('--cell', action='append', default=[])
        else:
            run.set_defaults(prepared=None, suite='full', primitive=[], backend=[], cell=[])
    plan = sub.add_parser('plan', help='List the selected cells and timed-work target without running anything')
    plan.add_argument('--prepared', type=Path, required=True)
    plan.add_argument('--suite', choices=['full', 'smoke', 'subset'], default='full')
    plan.add_argument('--primitive', action='append', default=[])
    plan.add_argument('--backend', action='append', default=[])
    plan.add_argument('--cell', action='append', default=[])
    args = parser.parse_args()
    try:
        if args.command == 'lock-references':
            reference_lock(args)
            return 0
        if args.command == 'plan':
            prepared = read(args.prepared / 'campaign.json')
            if prepared['state'] != 'prepared':
                raise ValueError('Plan requires a successful bootstrap')
            native = args.prepared / 'native'
            verify_prepared(native)
            print(json.dumps(selection.select(matrix(native, prepared['platform'])['cells'], prepared['platform'],
                                             args.suite, args.primitive, args.backend, args.cell), indent=2))
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
