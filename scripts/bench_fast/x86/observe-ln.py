#!/usr/bin/env python3
"""Observe exact timed ln inputs independently; no work here is timed.

mpmath at 600/1100 bits is an oracle observation, not a whole-domain proof.
Report uncertainty separately; reject a result whose error plus uncertainty
exceeds the published bound. All product backends must equal scalar bits.
"""
import ctypes as C
import hashlib
import json
import math
from pathlib import Path
import platform
import struct
import mpmath as mp

P=Path(__file__).resolve().parent
D=C.POINTER(C.c_double)
mp.mp.prec=1100
manifest=json.loads((P/'qualification-manifest.json').read_text())
arm=platform.system()=='Darwin'
native=C.CDLL(str(P/'bin/native-matrix.so'))
sleef=C.CDLL(str(P/'references'/('libsleef.3.9.0.dylib' if arm else 'libsleef.so.3')))
core_path=P/'references'/('libcorelog.dylib' if arm else 'libcorelog.so')
core=C.CDLL(str(core_path)) if core_path.exists() else None
keep=[native,sleef,core]

def bits(x):return struct.pack('>d',x).hex()
def scalar(lib,name):
    f=getattr(lib,name);f.argtypes=[C.c_double];f.restype=C.c_double;return f
def packet(lib,name,xs):
    f=getattr(lib,name);f.argtypes=[D,D,C.c_size_t];f.restype=None
    x=(C.c_double*max(1,len(xs)))(*xs);y=(C.c_double*max(1,len(xs)))()
    f(x,y,len(xs));return list(y)[:len(xs)]

reference={}
# Evaluate each exact input once at both independent working precisions.
for path in sorted((P/'inputs').glob('*.json')):
    for w in json.loads(path.read_text()):
        if w in reference:continue
        x=struct.unpack('>d',bytes.fromhex(w))[0]
        if not (x>0 and math.isfinite(x)):continue
        with mp.workprec(600):lo=mp.log(mp.mpf(x))
        exact=mp.log(mp.mpf(x))
        uncertainty=abs(exact-lo)+abs(exact)*mp.mpf(2)**-104+mp.mpf(2)**-1074
        cap=abs(exact)*mp.mpf(2)**-53+mp.mpf(2)**-65
        reference[w]=(exact,uncertainty,cap)

rows=[]
for build in manifest['builds']:
    lib=C.CDLL(build['product']);keep.append(lib)
    assert hashlib.sha256(Path(build['product']).read_bytes()).hexdigest()==build['sha256']
    fn=scalar(lib,'prod_ln');strong=scalar(lib,'control_ln');composed=scalar(lib,'prod_ln_exp')
    baseline=C.CDLL(build['control_product']) if build.get('control_product') else None
    if baseline:keep.append(baseline)
    for population in sorted((P/'inputs').glob('*.json')):
        words=json.loads(population.read_text());xs=[struct.unpack('>d',bytes.fromhex(w))[0] for w in words]
        ys=packet(lib,'prod_ln_slice',xs)
        expected=[fn(x) for x in xs]
        assert list(map(bits,ys))==list(map(bits,expected)),(build['name'],population.name)
        if baseline:
            assert list(map(bits,packet(lib,'control_ln_slice',xs)))==[bits(scalar(baseline,'control_ln')(x)) for x in xs]
        maximum=mp.mpf(0);witness=None;outputs=[]
        for w,x,y in zip(words,xs,ys):
            if w in reference:
                exact,uncertainty,cap=reference[w]
                fraction=(abs(mp.mpf(y)-exact)+uncertainty)/cap
                assert fraction<=1,(w,bits(y),str(fraction))
                if fraction>maximum:maximum,witness=fraction,w
                if x==1:assert bits(y)=='0000000000000000'
            else:assert bits(y)==bits(strong(x)),(w,bits(y))
            outputs.append(bits(y))
        rows.append(dict(backend=build['name'],population=population.stem,count=len(xs),
                         maximum_budget_fraction=str(maximum),witness=witness,
                         output_sha256=hashlib.sha256(bytes.fromhex(''.join(outputs))).hexdigest()))
    # Exercise exact calling lengths/remainders and references from the matrix.
    for c in [c for c in manifest['cells'] if c['backend']==build['name']]:
        words=json.loads(Path(c['input']['file']).read_text())
        xs=[struct.unpack('>d',bytes.fromhex(words[i%len(words)]))[0] for i in range(c['length'])]
        if c['control']:
            symbol='control_'+c['primitive']
            expected=[scalar(baseline,symbol)(x) for x in xs]
            got=packet(lib,symbol+'_slice',xs) if c['kind']=='vector' else [scalar(lib,symbol)(x) for x in xs]
            assert list(map(bits,got))==list(map(bits,expected)),c['id']
            rows.append(dict(cell=c['id'],control_identity=True,count=len(xs)))
            continue
        if c['primitive']=='ln_exp':
            errors=[]
            for x in xs:
                exact,uncertainty,_=reference[bits(x)]
                delta=(abs(exact)+uncertainty)*mp.mpf(2)**-53+mp.mpf(2)**-65
                cap=mp.expm1(delta)*(1+mp.mpf(2)**-51)+mp.mpf(2)**-51
                fraction=(abs(mp.mpf(composed(x))/mp.mpf(x)-1)+mp.mpf(2)**-104)/cap
                assert fraction<=1,(bits(x),str(fraction))
                errors.append(fraction)
            rows.append(dict(cell=c['id'],composition_maximum_budget_fraction=str(max(errors))))
            continue
        ours=[fn(x) for x in xs]
        if c['kind']=='vector':
            assert list(map(bits,packet(lib,'prod_ln_slice',xs)))==list(map(bits,ours)),c['id']
            values=packet(native,c['reference'],xs)
        else:
            ref=scalar(core,'cr_log') if c['reference']=='core_math_ln' else scalar(sleef,'Sleef_logd1_u10purec' if c['reference'].endswith('purec') else 'Sleef_logd1_u10purecfma')
            values=[ref(x) for x in xs]
        maximum=mp.mpf(0);witness=None
        for x,y in zip(xs,values):
            if bits(x) not in reference:continue
            exact,uncertainty,cap=reference[bits(x)]
            error=abs(mp.mpf(y)-exact)+uncertainty
            if c['reference']=='core_math_ln':assert bits(y)==bits(float(exact))
            if error/cap>maximum:maximum,witness=error/cap,bits(x)
        rows.append(dict(cell=c['id'],reference_maximum_product_budget_fraction=str(maximum),witness=witness,
                         reference_output_sha256=hashlib.sha256(b''.join(struct.pack('>d',y) for y in values)).hexdigest()))
(P/'oracle-observations.json').write_text(json.dumps(dict(mpmath=mp.__version__,precision_bits=[600,1100],
    uncertainty='|log_1100-log_600| + |log_1100|*2^-104 + 2^-1074',
    cells=rows),indent=2)+'\n')
print('Observed',len(reference),'distinct positive inputs;',len(rows),'bank/cell records; all product bounds and scalar/SIMD identities pass')
