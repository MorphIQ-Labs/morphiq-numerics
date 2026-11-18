#!/usr/bin/env python3
"""Stage canonical CDF comparisons on an existing candidate's exact input banks.

The full-CDF contract of each reference is distinct. These cells are diagnostic;
unchanged-domain qualification remains in the candidate's baseline matrix.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--references', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    source = json.loads((args.run/'qualification-manifest.json').read_text())
    references = json.loads((args.references/'references.json').read_text())
    if not (args.references/'accuracy.json').is_file():
        ap.error('Complete observe-cdf-references.py before staging timings')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ['qualify-cell.py','run-qualification.py','screen-ln.py','protocol.py','inputs.py','config.json']:
        shutil.copy2(args.run/name,out/name)
    shutil.copytree(args.run/'bin',out/'bin')
    (out/'references').mkdir()
    cells = []
    for original in source['cells']:
        if original['reference']!='baseline' or original['control']:
            continue
        length = 4096 if original['kind']=='vector' else 52
        if original['population'] not in ['far_negative','pricing'] or original['length']!=length:
            continue
        for reference in references['products']:
            if reference['backend']!=original['backend']:
                continue
            path = Path(reference['path'])
            assert hashlib.sha256(path.read_bytes()).hexdigest()==reference['sha256']
            cell = dict(original)
            cell.update(id=original['id'].removesuffix('-baseline')+'-'+reference['reference'],
                        reference=reference['reference'],reference_product=str(path),required_parity=False)
            cells.append(cell)
            source['binary_pins'][str(path)]=reference['sha256']
    if not cells:
        raise SystemExit('No matching candidate cells')
    source.update(cells=cells,execution_groups=[[c['id'] for c in cells]],
                  canonical_manifest=str((args.references/'references.json').resolve()),
                  canonical_accuracy=str((args.references/'accuracy.json').resolve()),
                  purpose='diagnostic complete-CDF cost and accuracy; not baseline qualification')
    (out/'qualification-manifest.json').write_text(json.dumps(source,indent=2)+'\n')
    print(f'Staged {len(cells)} cells in {out}')


if __name__=='__main__':
    main()
