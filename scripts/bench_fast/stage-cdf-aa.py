#!/usr/bin/env python3
"""Stage byte-identical CDF controls using an existing run's paired protocol.

Copies have distinct load addresses but identical bytes. These diagnostics
measure harness/process variation; they cannot establish product qualification.
"""
import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import shutil


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--cell', action='append', required=True,
                    help='Exact source cell ID; repeat to declare the diagnostic matrix')
    args = ap.parse_args()
    manifest_path = args.run/'qualification-manifest.json'
    source = json.loads(manifest_path.read_text())
    by_id = {cell['id']: cell for cell in source['cells']}
    if len(set(args.cell)) != len(args.cell) or any(c not in by_id for c in args.cell):
        ap.error('Select distinct existing cell IDs')
    selected = [by_id[c] for c in args.cell]
    if any(c['control'] or c['primitive'] != 'cdf' for c in selected):
        ap.error('Select CDF product cells, not strong controls')
    builds = {b['name']: b for b in source['builds']}
    for cell in selected:
        path = Path(cell['product'])
        if sha(path) != builds[cell['backend']]['sha256']:
            ap.error(f'Product changed: {path}')
        words = json.loads(Path(cell['input']['file']).read_text())
        if hashlib.sha256(b''.join(bytes.fromhex(w) for w in words)).hexdigest() != cell['input']['sha256']:
            ap.error(f'Input changed: {cell["id"]}')
    for name in ['native-matrix.so', 'native-cache.so']:
        timer = ctypes.CDLL(str((args.run/'bin'/name).resolve()))
        if not all(hasattr(timer, name) for name in ['bench_last_stack_address', 'bench_supported']):
            ap.error('Prepare a fresh run with the current native timers; preserve the older capsule')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ['qualify-cell.py', 'run-qualification.py']:
        shutil.copy2(Path(__file__).resolve().parent/'x86'/name, out/name)
    for name in ['protocol.py', 'inputs.py', 'config.json']:
        shutil.copy2(args.run/name, out/name)
    shutil.copytree(args.run/'bin', out/'bin')
    shutil.copytree(args.run/'references', out/'references')
    copies = {}
    cells = []
    pins = {}
    for original in selected:
        path = Path(original['product']).resolve()
        if path not in copies:
            copy = out/'bin'/f'aa-copy-{len(copies)}{path.suffix}'
            shutil.copy2(path, copy)
            if sha(path) != sha(copy):
                raise RuntimeError(f'Copy differs: {copy}')
            copies[path] = copy
        copy = copies[path]
        pins[str(path)] = sha(path)
        pins[str(copy)] = sha(copy)
        cell = dict(original)
        cell.update(id=original['id']+'-identical-binary', reference='identical-binary',
                    reference_product=str(copy), required_parity=False)
        cells.append(cell)
    source.update(cells=cells, execution_groups=[[c['id'] for c in cells]],
                  binary_pins=pins, stop_on_required_failure=False,
                  parent_manifest=str(manifest_path.resolve()),
                  parent_manifest_sha256=sha(manifest_path),
                  purpose='Byte-identical CDF diagnostic; not qualification')
    (out/'qualification-manifest.json').write_text(json.dumps(source, indent=2)+'\n')
    print(f'Staged {len(cells)} diagnostic cells in {out}')


if __name__ == '__main__':
    main()
