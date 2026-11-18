#!/usr/bin/env python3
"""Measure complete canonical CDF errors on the candidate's exact input banks.

Run with the pinned benchmark mpmath environment, outside native timings. These
are observations, not proofs of the canonical implementations' error bounds.
"""
import argparse
import ctypes as C
import hashlib
import json
import math
from pathlib import Path
import struct

import mpmath as mp


def bits(x):
    return struct.pack('>d', x).hex()


def value(word):
    return struct.unpack('>d', bytes.fromhex(word))[0]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--references', type=Path, required=True)
    args = ap.parse_args()
    assert mp.__version__ == '1.3.0', 'Use scripts/bench_fast/requirements.txt'
    manifest = json.loads((args.references/'references.json').read_text())
    run = json.loads((args.run/'qualification-manifest.json').read_text())
    words = set()
    for cell in run['cells']:
        words.update(json.loads(Path(cell['input']['file']).read_text()))
    fixtures = json.loads((Path(__file__).resolve().parents[2]/'crates/reference/fixtures/fast.json').read_text())
    words.update(row['x'] for row in fixtures['cases'] if row['primitive']=='cdf')
    xs = sorted((value(w) for w in words if math.isfinite(value(w))))
    oracles = []
    for x in xs:
        with mp.workprec(200):
            low = mp.erfc(-mp.mpf(x)/mp.sqrt(2))/2
        with mp.workprec(400):
            high = mp.erfc(-mp.mpf(x)/mp.sqrt(2))/2
            # Directed uncertainty is an observational guard, not a certificate.
            uncertainty = abs(high-low)+abs(high)*mp.mpf(2)**-180
            oracles.append((high, uncertainty))
    dptr = C.POINTER(C.c_double)
    xbuf, ybuf = (C.c_double*len(xs))(*xs), (C.c_double*len(xs))()
    rows = []
    for product in manifest['products']:
        path = Path(product['path'])
        assert hashlib.sha256(path.read_bytes()).hexdigest()==product['sha256']
        lib = C.CDLL(str(path))
        scalar = lib.prod_norm_cdf
        scalar.argtypes, scalar.restype = [C.c_double], C.c_double
        vector = lib.prod_norm_cdf_slice
        vector.argtypes, vector.restype = [dptr,dptr,C.c_size_t],None
        lib.reference_errors.restype=C.c_ulong
        vector(xbuf,ybuf,len(xs))
        row = dict(backend=product['backend'],reference=product['reference'],cases=len(xs),
                   scalar_slice_differences=0,regions={},specials={})
        for i,(x,(oracle,uncertainty)) in enumerate(zip(xs,oracles)):
            got = scalar(x)
            row['scalar_slice_differences'] += bits(got)!=bits(ybuf[i])
            region = 'far' if -22.5<=x<-8 else 'near' if 2**-33<=abs(x)<=8 else 'outside_fast_domain'
            data = row['regions'].setdefault(region,dict(count=0,max_absolute=0.,max_negative_relative_u=0.,nonfinite=0))
            data['count']+=1
            for interface,result in [('scalar',got),('slice',ybuf[i])]:
                if not math.isfinite(result):
                    data['nonfinite']+=1
                    continue
                with mp.workprec(400):
                    error = abs(mp.mpf(result)-oracle)+uncertainty
                    if error>data['max_absolute']:
                        data.update(max_absolute=float(error),absolute_witness=dict(x=bits(x),result=bits(result),interface=interface))
                    if x<0 and oracle>uncertainty and oracle>=mp.mpf(2)**-1022:
                        relative=error/(oracle-uncertainty)*2**53
                        if relative>data['max_negative_relative_u']:
                            data.update(max_negative_relative_u=float(relative),relative_witness=dict(x=bits(x),result=bits(result),interface=interface))
        for label,x in [('nan',float('nan')),('negative_infinity',-math.inf),('positive_infinity',math.inf),('negative_zero',-0.),('positive_zero',0.)]:
            row['specials'][label]=bits(scalar(x))
        row['caught_cpp_exceptions']=lib.reference_errors()
        rows.append(row)
        print(row['backend'],row['reference'],row['regions'].get('far'),flush=True)
    (args.references/'accuracy.json').write_text(json.dumps(dict(
        oracle='mpmath 1.3.0, 200/400 bits; observational uncertainty difference + abs(high)*2^-180',
        relative_scope='negative normal outputs; maximum across scalar and slice interfaces',
        inputs_sha256=hashlib.sha256(b''.join(bytes.fromhex(bits(x)) for x in xs)).hexdigest(),
        rows=rows),indent=2)+'\n')


if __name__=='__main__':
    main()
