#!/usr/bin/env python3
"""Build canonical CDF adapters outside native timings; retain source/build pins.

QuantLib files are fetched at a fixed revision after its license. Supply a Boost
1.86.0 tree and SLEEF 3.9.0 source/build from the pinned native benchmark setup.
Every used project header is hashed. No external code enters the library crate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import urllib.request

HERE = Path(__file__).resolve().parent
QUANTLIB = 'ab4cb476d35f7275834bc05b47d1324403d1823b'
SLEEF = '906ca7512ee483296780a81a21b9ca715d40dfe1'
BASE = f'https://raw.githubusercontent.com/lballabio/QuantLib/{QUANTLIB}/'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--boost', required=True, type=Path)
    ap.add_argument('--sleef-source', required=True, type=Path)
    ap.add_argument('--sleef-build', required=True, type=Path)
    args = ap.parse_args()
    out, boost, sleef_source, sleef_build = (x.resolve() for x in
        (args.out, args.boost, args.sleef_source, args.sleef_build))
    version = (boost/'boost/version.hpp').read_text()
    if not re.search(r'#define BOOST_VERSION\s+108600\b', version):
        ap.error('Boost 1.86.0 is required')
    if subprocess.check_output(['git','-C',str(sleef_source),'rev-parse','HEAD'],text=True).strip()!=SLEEF:
        ap.error('SLEEF source revision differs from the pinned 3.9.0 revision')
    if subprocess.check_output(['git','-C',str(sleef_source),'status','--porcelain']).strip():
        ap.error('SLEEF source must be clean')
    out.mkdir(parents=True, exist_ok=False)
    source = out/'quantlib'; source.mkdir()
    manifest = dict(quantlib=dict(version='1.44',revision=QUANTLIB,files={}),
        boost=dict(version='1.86.0',archive_url='https://archives.boost.io/release/1.86.0/source/boost_1_86_0.tar.bz2',
                   archive_sha256='1bed88e40401b2cb7a1f76d4bab499e352fa4d0c5f31c0dbae64e24d34d7513b',
                   supplied_tree=str(boost),used_headers={}),
        sleef=dict(version='3.9.0',revision=SLEEF,build=str(sleef_build)),
        commands=[],products=[],compiler=subprocess.check_output(['c++','--version'],text=True))
    def save(): (out/'references.json').write_text(json.dumps(manifest,indent=2)+'\n')
    def fetch(name):
        dest=source/name
        if dest.exists(): return
        # config.hpp is generated only when HAVE_CONFIG_H is defined; this
        # standalone reference build uses QuantLib's supported default defines.
        if name=='ql/config.hpp': return
        data=urllib.request.urlopen(BASE+name,timeout=60).read()
        dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        manifest['quantlib']['files'][name]=sha(dest);save()
        for dep in re.findall(rb'#\s*include\s*[<"](ql/[^>"]+)[>"]',data):fetch(dep.decode())
    fetch('LICENSE.TXT')
    for name in ('ql/math/distributions/normaldistribution.cpp','ql/math/errorfunction.cpp','ql/errors.cpp'):
        fetch(name)
    license_path = boost/'LICENSE_1_0.txt'
    license_bytes = license_path.read_bytes() if license_path.exists() else urllib.request.urlopen(
        'https://raw.githubusercontent.com/boostorg/boost/65c1319bb92fe7a9a4abd588eff5818d9c2bccf9/LICENSE_1_0.txt', timeout=60).read()
    (out/'BOOST_LICENSE_1_0.txt').write_bytes(license_bytes)
    manifest['boost']['supplied_archive_verified'] = False
    manifest['boost']['license_sha256'] = sha(out/'BOOST_LICENSE_1_0.txt')
    (out/'SLEEF_LICENSE.txt').write_bytes((sleef_source/'LICENSE.txt').read_bytes())
    mac=platform.system()=='Darwin'
    arm=platform.machine() in ('aarch64','arm64')
    products=[('auto',[],2)] if arm else [('auto',['-march=x86-64-v3'],8),('avx2',['-march=x86-64-v3'],4),('avx512',['-march=x86-64-v4'],8)]
    if not arm:
        flags=Path('/proc/cpuinfo').read_text()
        if 'avx512f' not in flags: products[0]=('auto',['-march=x86-64-v3'],4)
    sleef_lib=sleef_build/'lib'/('libsleef.dylib' if mac else 'libsleef.so')
    manifest['sleef']['binary_sha256']=sha(sleef_lib)
    manifest['sleef']['cmake_cache_sha256']=sha(sleef_build/'CMakeCache.txt')
    wrapper=HERE/'cdf-reference-wrapper.cpp'
    manifest['wrapper_sha256']=sha(wrapper)
    for backend,flags,width in products:
        for kind,label in enumerate(('quantlib','boost-default','boost-binary64','sleef-erfc')):
            dest=out/f'{backend}-{label}.so'
            command=['c++','-std=c++17','-O3','-flto','-fPIC','-dynamiclib' if mac else '-shared','-ffp-contract=off',*flags,
                     f'-DCDF_REFERENCE={kind}',f'-DCDF_LANES={width}','-I'+str(source),'-I'+str(boost),'-I'+str(sleef_build/'include'),str(wrapper)]
            if kind==0: command += [str(source/n) for n in ('ql/math/distributions/normaldistribution.cpp','ql/math/errorfunction.cpp','ql/errors.cpp')]
            if kind==3: command += ['-L'+str(sleef_build/'lib'),'-Wl,-rpath,'+str(sleef_build/'lib'),'-lsleef']
            command += ['-o',str(dest)]
            manifest['commands'].append(command);save()
            with (out/f'{backend}-{label}.log').open('w') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
            # Pin every Boost header the preprocessor actually uses.
            dependencies=subprocess.check_output(command[:command.index(str(wrapper))]+['-MM',str(wrapper)],text=True)
            for filename in dependencies.replace('\\\n',' ').split():
                f=Path(filename)
                if f.is_file() and f.is_relative_to(boost):manifest['boost']['used_headers'][str(f.relative_to(boost))]=sha(f)
            manifest['products'].append(dict(backend=backend,reference=label,path=str(dest),sha256=sha(dest),
                interface='native SIMD with scalar remainders' if kind==3 else 'scalar loop for slices',
                cpp_flags=flags,fp_contract='off'))
            save()
            print(backend,label,flush=True)
    save()


if __name__=='__main__':main()
