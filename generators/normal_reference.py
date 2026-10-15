#!/usr/bin/env python3
"""Independent normal-family witnesses at 600 and 1000 bits.

References use the defining Gaussian density, erf and erfc. Large negative
log-CDF uses an arbitrary-precision Mills expansion, with a first-omitted-term
screen, to avoid forming a probability with an astronomically large exponent.
Every binary64 result is rounded once on its final normal/subnormal grid.
"""
import json
import math
import pathlib
import random
import struct
import sys
import mpmath as mp

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'crates/reference/fixtures/normal.json'
NAMES = ['pdf', 'cdf', 'ccdf', 'centered', 'log_cdf']

# Rounding-sensitive inputs discovered by normal_find_rounding_witnesses.
# Expected values are independently regenerated below, never copied from Rust.
HARD_INPUTS = [
    '403dac11bd9d4430',
    'c04149f615e7d94b',
    '402d850503c0c448',
    '403ce841087f6cdc',
    '4040ae64863f4ace',
    '40404985cef41b08',
    'c03bf1052e337908',
    'c0422dede90f55e2',
    '4041cee78bbb86be',
    '40420272f0b52b78',
    '4040ce3a50e75d2c',
    'c03671d8695a2a38',
    'c0349bea386752fb',
    '403a76f04d5a14f6',
    'c03f8c47abf0b1fa',
    '40225f6919779fa4',
    'c03dd0bf9bd62dc6',
    'c038dd63d047a4ae',
    'c04086152fd34c59',
    '4039d5306cf6428a',
    'c04013cd4a399b72',
    'c03fe0f6292310da',
    'c006df3c601603a0',
    'c03ab4ecaf750b8d',
    '403e3f432257f498',
    'c036e4399d0e3ce5',
    'c0346a3d703ce381',
    '4041171a87a323ea',
    '402754b3f4cacbc0',
    'c0409107199064b6',
    '40271f9b52114964',
    '403da4f9f622f0e4',
    '40420660cc0d2e60',
    '4033586692541aba',
    'c040633b59895ff4',
    'c03a728d4a92e4f9',
    'c0423f1eb6125b2f',
    'c04228ecfd51d2c1',
    'c03d8ab24566132b',
    'c03e9f675a19a521',
    'c040afe3c7dc5ade',
    '4030eb5151617a56',
    'c04011f6fa60715b',
    '4037c2ceb3524272',
    '40375ebd98267b00',
    'c040b0aac6802280',
    'bfdf68872d8d9830',
    '4041de3f6bc7785c',
    'c041bbc9fe34a54a',
]

def bits(x):
    return struct.pack('>d', x).hex()

def number(b):
    return struct.unpack('>d', bytes.fromhex(b))[0]

def rounded(v):
    negative = v < 0
    v = abs(v)
    if v == 0 or v < mp.ldexp(1, -1076):
        return -0.0 if negative else 0.0
    if v > mp.ldexp(1, 1024):
        return -math.inf if negative else math.inf
    m, e = v.man_exp
    m, e = int(m), int(e)
    quantum = max(m.bit_length() - 1 + e - 52, -1074)
    shift = quantum - e
    if shift > 0:
        kept, rem = divmod(m, 1 << shift)
        half = 1 << (shift - 1)
        if rem > half or (rem == half and kept & 1): kept += 1
    else: kept = m << -shift
    try: y = math.ldexp(float(kept), quantum)
    except OverflowError: y = math.inf
    return -y if negative else y

def large_log_tail(a, precision):
    t = 1/(a*a)
    term, total = mp.mpf(1), mp.mpf(1)
    for n in range(1, 2000):
        term *= -(2*n-1)*t
        if abs(term) < mp.ldexp(1, -precision-32):
            return -a*a/2-mp.log(a)-mp.log(2*mp.pi)/2+mp.log(total)
        total += term
    raise AssertionError('tail remainder failed')

def values(x, precision):
    if math.isnan(x): return [bits(x)] * 5
    if math.isinf(x):
        return list(map(bits, [0., 1. if x>0 else 0., 0. if x>0 else 1.,
                              math.copysign(.5,x), -0. if x>0 else -math.inf]))
    with mp.workprec(precision):
        z = mp.mpf(x)
        a = abs(z)
        if a >= 40:
            ys = [0., 1. if x>0 else 0., 0. if x>0 else 1., math.copysign(.5,x),
                  -0. if x>0 else rounded(large_log_tail(a, precision))]
        else:
            s = z/mp.sqrt(2)
            pdf = mp.exp(-z*z/2)/mp.sqrt(2*mp.pi)
            cdf = mp.erfc(-s)/2
            ccdf = mp.erfc(s)/2
            centered = mp.erf(s)/2
            logcdf = mp.log(cdf) if x<=0 else mp.log1p(-ccdf)
            ys = [rounded(y) for y in [pdf,cdf,ccdf,centered,logcdf]]
        if ys[3] == 0: ys[3] = math.copysign(0.,x)
        if ys[4] == 0: ys[4] = -0.
        return list(map(bits,ys))

def thresholds():
    with mp.workprec(1000):
        def logtail(x): return mp.log(mp.erfc(x/mp.sqrt(2))/2)
        return {
            'pdf_zero': float(mp.sqrt(2*(1075*mp.log(2)-mp.log(2*mp.pi)/2))),
            'tail_zero': float(mp.findroot(lambda x: logtail(x)+1075*mp.log(2), (38,39))),
            'cdf_one': float(mp.findroot(lambda x: logtail(x)+54*mp.log(2), (8,9))),
            'centered_half': float(mp.findroot(lambda x: logtail(x)+55*mp.log(2), (8,9))),
            'log_overflow': float(mp.sqrt(2*(mp.ldexp(1,1024)-mp.ldexp(1,970))))}

def extended_erfcx():
    cases=[]
    for high in [0.5, 1., 2., 4.] + [8.+i/4 for i in range(33)]:
        for low in [-2.**-100, 0., 2.**-100]:
            results=[]
            for precision in [600,1000]:
                with mp.workprec(precision):
                    x=mp.mpf(high)+mp.mpf(low)
                    results.append(bits(rounded(mp.exp(x*x)*mp.erfc(x))))
            assert results[0]==results[1]
            cases.append({'hi':bits(high),'lo':bits(low),'erfcx':results[0]})
    return cases

def main():
    thresholds_ = thresholds()
    points = [0.,-0.,.1,-.1,1.,-1.,math.inf,-math.inf,
              number('7ff8000000001234'),number('fff8000000005678'),number('7ff0000000004321')]
    points += [number(b) for b in HARD_INPUTS]
    edges = [.5, 9., 16*math.sqrt(2), 37., 40., 2.**-33,2.**-450]
    edges += list(thresholds_.values())
    edges += [math.ldexp(1.,e) for e in [-1074,-1073,-1022,-500,-450,-100,-60,-55,-54,-53,-33,-27,-1,0,3,5,26,500,511,512,513,1023]]
    edges += [math.sqrt(2)*i/32 for i in range(33)]
    def add_neighbors(edges):
        for c in edges:
            for sign in [1.,-1.]:
                x=sign*c;points.append(x)
                low=high=x
                for _ in range(3):
                    low=math.nextafter(low,-math.inf);high=math.nextafter(high,math.inf)
                    points.extend([low,high])
    add_neighbors(edges)
    rng = random.Random(0x35_cdf)
    for _ in range(384):
        points += [rng.uniform(-.5,.5),rng.uniform(-9,9),rng.uniform(-40,40),
                   math.ldexp(rng.uniform(-1,1),rng.randrange(-1073,-27)),
                   -math.ldexp(rng.uniform(1,2),rng.randrange(6,1023))]
    add_neighbors([2.**44, 2.**45, 2.**46])
    # Exercise the far log-CDF tail, including the narrow unsaturated bands
    # of the sibling functions and both sides of the scaled-square split.
    for _ in range(256):
        a = rng.uniform(37, 39)
        points += [-a, a, -math.ldexp(rng.uniform(1, 2), rng.randrange(6, 513))]
    # Deduplicate by encoding, preserving both zero signs and distinct NaNs.
    points = list(dict.fromkeys(bits(x) for x in points))
    cases=[]
    for b in points:
        x=number(b);a=values(x,600);z=values(x,1000)
        assert a==z,(b,a,z)
        cases.append(dict(x=b,**dict(zip(NAMES,a))))
    data={'provenance':{'generator':'generators/normal_reference.py','mpmath':mp.__version__,
                        'precisions':[600,1000]},'threshold_neighbors':{k:bits(v) for k,v in thresholds_.items()},
          'extended_erfcx':extended_erfcx(),'cases':cases}
    text=json.dumps(data,indent=2)+'\n'
    if '--check' in sys.argv: assert OUT.read_text()==text,'normal fixture differs'
    else: OUT.write_text(text)
    print(f'normal: {len(cases)} independent witnesses per function')

if __name__ == '__main__': main()
