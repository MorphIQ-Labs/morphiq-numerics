#!/usr/bin/env python3
"""Freeze source, generated inputs, harness and linked libraries before timing."""
import argparse, hashlib, json, subprocess
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('run',type=Path)
ap.add_argument('--verify',action='store_true')
a=ap.parse_args();p=a.run.resolve();receipt=p/'source.json'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
if a.verify:
    m=json.loads(receipt.read_text())
    for name,h in m['files'].items():
        if sha(Path(name))!=h:raise SystemExit('Frozen file changed: '+name)
    print('Frozen files verified')
else:
    if receipt.exists():raise SystemExit('Receipt already exists; use a fresh run directory')
    repo=Path(__file__).resolve().parents[2]
    source=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    dirty=subprocess.check_output(['git','-C',str(repo),'status','--porcelain'],text=True).strip()
    if dirty:raise SystemExit('Commit methodology/source changes before freezing qualification')
    files=[f for f in p.rglob('*') if f.is_file() and '__pycache__' not in f.parts and not any(part in ['qualified','qualification','host'] for part in f.relative_to(p).parts)]
    # Explicitly include external shared libraries, even when referenced through symlinks.
    files += [f for f in (p/'references').iterdir() if f.is_file()]
    files += [repo/n for n in subprocess.check_output(['git','-C',str(repo),'ls-files','crates/morphiq-numerics','crates/morphiq-numerics-arch','scripts/bench_fast','Cargo.toml','Cargo.lock','rust-toolchain.toml'],text=True).splitlines()]
    receipt.write_text(json.dumps(dict(commit=source,files={str(f.resolve()):sha(f) for f in sorted(set(files))}),indent=2)+'\n')
    print('Frozen',source,len(files),'files')
