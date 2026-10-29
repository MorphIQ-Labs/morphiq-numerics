#!/usr/bin/env python3
"""Prepare native ln scalar/SIMD comparisons; no timings or oracles during builds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
from importlib.util import spec_from_file_location, module_from_spec

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--reference-bin', type=Path, required=True)
    ap.add_argument('--cpu', type=int, default=2)
    ap.add_argument('--full', action='store_true')
    ap.add_argument('--platform', choices=['x86-linux','arm-macos'], default='x86-linux')
    ap.add_argument('--control-source', type=Path)
    ap.add_argument('--sleef-include', type=Path)
    args = ap.parse_args()
    arm = args.platform=='arm-macos'
    expected = ('Darwin','arm64') if arm else ('Linux','x86_64')
    if (platform.system(),platform.machine())!=expected:
        ap.error('Use the declared native host; emulation is not qualification')
    if not arm:
        flags = Path('/proc/cpuinfo').read_text()
        if 'avx512f' not in flags or 'fma' not in flags:
            ap.error('The x86 matrix requires AVX-512F and FMA')
    if arm and not args.sleef_include: ap.error('--sleef-include is required on ARM')
    if args.full and not args.control_source: ap.error('--full requires a clean --control-source')
    out = args.out.resolve()
    out.relative_to((ROOT/'target').resolve())
    refs = args.reference_bin.resolve()
    names = ['libsleef.3.9.0.dylib'] if arm else ['libsleef.so.3','libsleef.so']
    if args.full: names += ['libcorelog.dylib' if arm else 'libcorelog.so']
    for name in names:
        if not (refs/name).is_file(): ap.error('Missing pinned reference: '+str(refs/name))
    metadata = dict(cpu=args.cpu, platform=args.platform)
    sources = [('source',ROOT)]
    if args.control_source: sources.append(('control',args.control_source.resolve()))
    for label,source in sources:
        if subprocess.check_output(['git','status','--porcelain'],cwd=source,text=True).strip():
            ap.error(label+' checkout must be committed and clean')
        metadata[label+'_commit']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()
    out.mkdir(parents=True,exist_ok=False)
    (out/'bin').mkdir()
    (out/'references').symlink_to(refs,target_is_directory=True)
    for name in ['qualify-cell.py','run-qualification.py','ln-matrix.py','observe-ln.py','screen-ln.py']:
        shutil.copy2(HERE/name,out/name)
    for name in ['inputs.py','protocol.py']: shutil.copy2(HERE.parent/name,out/name)
    (out/'config.json').write_text(json.dumps(metadata,indent=2)+'\n')
    commands=[]
    def run(command,**kwargs):
        commands.append(dict(argv=command, rustflags=kwargs.get('env',{}).get('RUSTFLAGS')))
        (out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
        subprocess.run(command,check=True,**kwargs)
    def build(source,backend,features,flags,label):
        folder=out/(label+'-wrapper-'+backend)
        shutil.copytree(HERE/'ln-wrapper',folder)
        (folder/'Cargo.toml').write_text('''[package]
name="ln-bench-wrapper"
version="0.0.0"
edition="2024"
[workspace]
[lib]
crate-type=["cdylib"]
[dependencies]
morphiq-numerics={path='''+json.dumps(str(source/'crates/morphiq-numerics'))+''',default-features=false,features='''+json.dumps(features.split(','))+'''}
[profile.release]
lto="thin"
codegen-units=1
''')
        env=dict(os.environ,CARGO_TARGET_DIR=str(out/(label+'-build-'+backend)),RUSTFLAGS=flags)
        for key in ['CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_BUILD_TARGET','CARGO_BUILD_RUSTFLAGS']:env.pop(key,None)
        run(['cargo','build','--release','--manifest-path',str(folder/'Cargo.toml')],env=env)
        product=out/(label+'-build-'+backend)/'release'/('libln_bench_wrapper.'+('dylib' if arm else 'so'))
        dest=out/'bin'/(label+'-'+backend+'.so')
        shutil.copy2(product,dest)
        return dest
    configs=[('auto','simd,std','')]
    if args.full and not arm:
        configs += [('sse2','simd','-C target-feature=-avx,-avx2,-avx512f,-fma'),
                    ('avx2','simd','-C target-feature=+avx2,+fma,-avx512f'),
                    ('avx512','simd','-C target-feature=+avx512f,+avx2,+fma')]
    builds=[]
    digest=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
    for backend,features,flags in configs:
        product=build(ROOT,backend,features,flags,'candidate')
        item=dict(name=backend,features=features,rustflags=flags,product=str(product),sha256=digest(product))
        if args.full:
            control=build(args.control_source.resolve(),backend,features,flags,'control')
            item.update(control_product=str(control),control_sha256=digest(control))
        builds.append(item)
    for timer in ['native-matrix','native-cache']:
        command=['cc','-O3','-fPIC','-dynamiclib' if arm else '-shared','-ffp-contract=off',str(HERE/(timer+'.c'))]
        if timer=='native-matrix':
            if arm: command+=['-I',str(args.sleef_include.resolve()),str(refs/'libsleef.3.9.0.dylib')]
            else: command+=['-L'+str(refs),'-lsleef']
            command+=['-Wl,-rpath,'+str(refs)]
        run(command+['-o',str(out/'bin'/(timer+'.so'))])
    spec=spec_from_file_location('ln_matrix',HERE/'ln-matrix.py')
    module=module_from_spec(spec);spec.loader.exec_module(module)
    cells=module.matrix(out,builds,arm,args.full)
    manifest=dict(scope='Full native ln matrix' if args.full else 'Three ordinary cells only',
                  source_commit=metadata['source_commit'],control_commit=metadata.get('control_commit'),
                  builds=builds,cells=cells,stop_on_required_failure=args.full,
                  reference_sha256={name:digest(refs/name) for name in names},
                  protocol=dict(upper95_t9=1.8331129326536335))
    (out/'qualification-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(out, len(cells),'cells',sum(c['required_parity'] for c in cells),'required')


if __name__=='__main__': main()
