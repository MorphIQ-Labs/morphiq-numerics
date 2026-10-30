#!/usr/bin/env python3
"""Observe final Linux ln binaries with gperftools; never run during timings.

Preload libtcmalloc.so.4 and pass a prepared run plus allocation-probe.so.
The C probe brackets only public calls. Python buffers and parsing are outside
profiling. A 71-byte allocate/free positive control must be observed exactly.
"""
import argparse
import ctypes as C
import hashlib
import json
from pathlib import Path
import re
import struct

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('run', type=Path)
ap.add_argument('probe', type=Path)
a = ap.parse_args()
p = a.run.resolve()
out = p/'allocation-observations'
out.mkdir(exist_ok=False)
manifest = json.loads((p/'qualification-manifest.json').read_text())
probe = C.CDLL(str(a.probe.resolve()))
D = C.POINTER(C.c_double)
probe.observe_control.argtypes = [C.c_char_p]
probe.observe_control.restype = None
probe.observe_allocations.argtypes = [C.c_void_p,D,D,C.c_size_t,C.c_int,C.c_char_p]
probe.observe_allocations.restype = None


def counts(prefix):
    files = list(out.glob(prefix.name+'.*.heap'))
    assert len(files) == 1, files
    match = re.search(r'heap profile:\s+(\d+):\s+(\d+)\s+\[\s*(\d+):\s+(\d+)\]', files[0].read_text())
    assert match, files[0]
    return [int(v) for v in match.groups()]


control = out/'positive-control'
probe.observe_control(str(control).encode())
assert counts(control) == [0,0,1,71], counts(control)
rows = []
for build in manifest['builds']:
    product = Path(build['product'])
    assert hashlib.sha256(product.read_bytes()).hexdigest() == build['sha256']
    lib = C.CDLL(str(product))
    for population in ['ordinary','wide','near_one','subnormal','mixed_positive','mixed_special']:
        words = json.loads((p/'inputs'/(population+'.json')).read_text())
        for n in [1,9,52,4096]:
            x = (C.c_double*n)(*(struct.unpack('>d',bytes.fromhex(words[i%len(words)]))[0] for i in range(n)))
            for scalar in [True,False]:
                symbol = 'prod_ln' + ('' if scalar else '_slice')
                fn = getattr(lib,symbol)
                y = (C.c_double*n)()
                prefix = out/f'{build["name"]}-{population}-{n}-{symbol}'
                probe.observe_allocations(C.cast(fn,C.c_void_p),x,y,n,int(scalar),str(prefix).encode())
                observed = counts(prefix)
                reference = lib.prod_ln
                reference.argtypes = [C.c_double]
                reference.restype = C.c_double
                assert bytes(y) == bytes((C.c_double*n)(*(reference(v) for v in x)))
                rows.append(dict(backend=build['name'],product_sha256=build['sha256'],population=population,
                                 length=n,symbol=symbol,calls=10001*(n if scalar else 1),counts=observed))
result = dict(positive_control=counts(control),cells=rows,
              limitation='Native Linux gperftools heap hooks; excludes caller buffers and Python. Instrumented calls are never timing evidence.')
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
assert all(r['counts']==[0,0,0,0] for r in rows)
print(len(rows),'public-call populations: zero allocation events; positive control detected')
