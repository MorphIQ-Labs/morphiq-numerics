#!/usr/bin/env python3
"""Materialize the established native harness in a fresh ignored run directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--platform', choices=['arm-macos','x86-linux'], required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--reference-bin', type=Path, required=True)
    ap.add_argument('--sleef-include', type=Path)
    ap.add_argument('--control-source', type=Path)
    ap.add_argument('--cpu', type=int, default=2)
    args = ap.parse_args()
    arm = args.platform == 'arm-macos'
    if (arm and (platform.system()!='Darwin' or platform.machine()!='arm64')) or (not arm and (platform.system()!='Linux' or platform.machine()!='x86_64')):
        ap.error('Use the declared native host; emulation is not qualification')
    if arm and not args.sleef_include:
        ap.error('--sleef-include is required on ARM')
    if not arm and not args.control_source:
        ap.error('--control-source must name a clean baseline checkout on x86')
    out = args.out.resolve()
    # All generated files, libraries and raw measurements stay in ignored target/.
    out.relative_to(REPO/'target')
    references = args.reference_bin.resolve()
    names = ['libcoreexp.dylib','libcerf.3.1.dylib','libsleef.3.9.0.dylib','libsleef.3.dylib'] if arm else ['libcoreexp.so','libcerf.so','libsleef.so.3','libsleef.so']
    for name in names:
        if not (references/name).is_file():ap.error(f'Missing reference: {references/name}')
    out.mkdir(parents=True, exist_ok=False)
    shutil.copytree(HERE/('arm' if arm else 'x86'), out, dirs_exist_ok=True)
    for name in ['inputs.py','protocol.py']:shutil.copy2(HERE/name,out/name)
    (out/'bin').mkdir()
    (out/'references').symlink_to(references, target_is_directory=True)
    if arm:
        for name in names:(out/'bin'/name).symlink_to(references/name)
    metadata=dict(cpu=args.cpu, platform=args.platform)
    for label,source in [('source',REPO)]+([('control',args.control_source.resolve())] if args.control_source else []):
        if subprocess.check_output(['git','-C',str(source),'status','--porcelain'],text=True).strip():
            ap.error(f'{label} checkout must be clean before building')
        metadata[label+'_commit']=subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip()
    (out/'config.json').write_text(json.dumps(metadata,indent=2)+'\n')
    records=[]
    def run(command,cwd=out,env=None):
        records.append(command)
        (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
        subprocess.run(command,cwd=cwd,env=env,check=True)
    def build(folder,source,name,features,flags,target):
        path=out/folder
        crate=source/'crates/morphiq-numerics'
        manifest=f'''[package]
name="{name}"
version="0.0.0"
edition="2024"
[workspace]
[lib]
crate-type=["cdylib"]
[dependencies]
morphiq-numerics={{path={json.dumps(str(crate))},default-features=false}}
[features]
simd=["morphiq-numerics/simd"]
std=["morphiq-numerics/std"]
[profile.release]
lto="thin"
codegen-units=1
'''
        (path/'Cargo.toml').write_text(manifest)
        env=dict(os.environ)
        for key in ['CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_BUILD_TARGET','CARGO_BUILD_RUSTFLAGS']:env.pop(key,None)
        env.update(RUSTFLAGS=flags,CARGO_TARGET_DIR=str(out/target))
        run(['cargo','build','--release','--no-default-features','--features',features],path,env)
        ext='dylib' if arm else 'so'
        return out/target/'release'/('lib'+name.replace('-','_')+'.'+ext)
    if arm:
        prod=build('wrapper',REPO,'production-bench-wrapper','simd,std','','build')
        shutil.copy2(prod,out/'bin'/prod.name)
        build('allocation-wrapper',REPO,'allocation-observation-wrapper','simd,std','','allocation-build')
        run(['cc','-O3','-fPIC','-dynamiclib','-ffp-contract=off','-I',str(args.sleef_include.resolve()),str(out/'native.c'),str(references/'libsleef.3.9.0.dylib'),str(prod),'-Wl,-rpath,'+str(references),'-o',str(out/'bin/libnativebench.dylib')])
        run([sys.executable,str(out/'matrix.py')])
        cells=json.loads((out/'cells.json').read_text())
        critical=['014','015','016']+[f'{i:03d}' for i in range(31,48)]+[f'{i:03d}' for i in range(154,158)]
        (out/'groups.json').write_text(json.dumps(dict(critical=critical,remaining=[c['id'] for c in cells if c['id'] not in critical]),indent=2)+'\n')
    else:
        builds=[];(out/'qualification-bin').mkdir();(out/'final-bin').mkdir()
        for name,features,flags in [('auto','simd,std',''),('sse2','simd','-C target-feature=-avx,-avx2,-avx512f,-fma'),('avx2','simd','-C target-feature=+avx2,+fma,-avx512f'),('avx512','simd','-C target-feature=+avx512f,+avx2,+fma')]:
            product=build('matrix-wrapper',REPO,'matrix-bench-wrapper',features,flags,'build-'+name)
            destination=out/'qualification-bin'/(name+'.so');shutil.copy2(product,destination)
            builds.append(dict(name=name,features=features,rustflags=flags,sha256=hashlib.sha256(destination.read_bytes()).hexdigest()))
        shutil.copytree(out/'matrix-wrapper',out/'control-wrapper')
        product=build('control-wrapper',args.control_source.resolve(),'control-bench-wrapper','simd,std','','control-build')
        shutil.copy2(product,out/'final-bin/control.so')
        (out/'qualification-builds.json').write_text(json.dumps(builds,indent=2)+'\n')
        run(['cc','-O3','-fPIC','-shared','-ffp-contract=off',str(out/'native-matrix.c'),'-L'+str(references),'-Wl,-rpath,'+str(references),'-lsleef','-o',str(out/'bin/native-matrix.so')])
        run(['cc','-O3','-fPIC','-shared','-ffp-contract=off',str(out/'native-cache.c'),'-o',str(out/'bin/native-cache.so')])
        run([sys.executable,str(out/'prepare-qualification.py')])
    print(f'Prepared {out}. Run observations, freeze.py, then the native runner as documented.')

if __name__=='__main__':main()
