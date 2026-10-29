"""Exact ln banks and predeclared cells; generated timings never enter Git."""
import hashlib
import json
from pathlib import Path
import struct


def word(x):
    return struct.pack('>d', x).hex()


def banks():
    mask = (1 << 52) - 1
    ordinary = [word(.5 + 1.5*i/51) for i in range(52)]
    wide = [f'{((1+(i*503)%2046)<<52) | ((i*0x9e3779b97f4a7c15)&mask):016x}' for i in range(4096)]
    near = [f'{(0x3ff0000000000000+d):016x}' for d in list(range(-128, 129)) + [-(1<<k) for k in range(8, 42)] + [1<<k for k in range(8, 42)]]
    sub = [f'{v:016x}' for v in [1, 2, 3, mask, mask-1] + [1<<k for k in range(52)] + [1+(i*0x9e3779b97f4a7c15)%mask for i in range(512)]]
    # Powers of two, reduction/table transitions and adjacent encodings.
    boundary = [f'{v+d:016x}' for v in [(e<<52) for e in range(1, 2047, 17)] + [0x3fe6a00000000000+(i<<43) for i in range(512)] for d in [-1, 0, 1] if 0 < v+d < 0x7ff0000000000000]
    mixed = [values[i % len(values)] for i in range(4096) for values in [ordinary, wide, near, sub, boundary]]
    special = ['0000000000000000', '8000000000000000', 'bff0000000000000', '7ff0000000000000', 'fff0000000000000', '7ff8000000000001', '7ff0000000000001']
    mixed_special = [special[(i//16)%len(special)] if i%16==0 else ordinary[i%52] for i in range(4096)]
    composition = [f'{((123+(i*719)%1801)<<52) | ((i*0x9e3779b97f4a7c15)&mask):016x}' for i in range(4096)]
    ln1p_fallback = [word(-1.+2.**-k) for k in range(1,53)] + [word(2.**e) for e in range(0,1024,31)] + [word(s*2.**-e) for s in [-1,1] for e in [54,128,1022]]
    return dict(ln1p_fallback=ln1p_fallback, ordinary=ordinary, wide=wide, near_one=near, subnormal=sub,
                boundary=boundary, mixed_positive=mixed, special=special,
                mixed_special=mixed_special, composition=composition)


def matrix(out, builds, arm, full):
    out = Path(out)
    directory = out/'inputs'
    directory.mkdir()
    bank = {}
    for name, words in banks().items():
        path = directory/(name+'.json')
        path.write_text(json.dumps(words)+'\n')
        bank[name] = dict(file=str(path), length=len(words),
                          sha256=hashlib.sha256(bytes.fromhex(''.join(words))).hexdigest())
    cells = []
    def add(backend, population, length, kind='vector', reference=None,
            required=True, control=False, slots=1, primitive='ln'):
        build = next(b for b in builds if b['name']==backend)
        vector_ref = 'neon' if arm else ('avx512' if backend=='auto' else backend)
        # The public wrapper selects a narrower backend for short inputs.
        if not arm and backend != 'sse2':
            if length < 4: vector_ref='sse2'
            elif length < 8 and vector_ref=='avx512': vector_ref='avx2'
        scalar_ref = 'sleef_ln_scalar_purec' if backend=='sse2' else 'sleef_ln_scalar_fma'
        reference = reference or (('sleef_ln_'+vector_ref) if kind=='vector' else scalar_ref)
        ident = '-'.join(map(str, [primitive, backend, population, length, kind, reference]))
        if control: ident+='-control'
        if slots!=1: ident+='-cache'+str(slots)
        cells.append(dict(id=ident, primitive=primitive, backend=backend,
                          population=population, length=length, kind=kind,
                          reference=reference, required_parity=required and length>0,
                          control=control, cache_slots=slots, input=bank[population],
                          product=build['product'], control_product=build.get('control_product')))
    if not full:
        for kind in ['scalar','latency','vector']:
            add('auto','ordinary',52,kind)
        return cells
    regions = ['ordinary','wide','near_one','subnormal','boundary','mixed_positive']
    # Critical representative cells precede the longer dispatch matrix.
    for backend in [b['name'] for b in builds]:
        for region in regions:
            for n in [52,4096]: add(backend,region,n)
        for region in ['special','mixed_special']:
            for n in [52,4096]: add(backend,region,n,required=False)
        for region in regions:
            for n in [52,4096]: add(backend,region,n,control=True,required=False)
        if backend!='auto':
            for kind in ['scalar','latency']: add(backend,'ordinary',52,kind)
    for region in regions:
        for kind in ['scalar','latency']:
            for reference in ['sleef_ln_scalar_fma','core_math_ln']:
                add('auto',region,52,kind,reference)
            add('auto',region,52,kind,control=True,required=False)
    for backend in [b['name'] for b in builds]:
        lengths = list(range(18)) + ([31,32,33,51,53,63,64,65,256,65536] if backend=='auto' else [65536])
        for region in ['ordinary','wide']:
            for n in lengths: add(backend,region,n)
    for slots in [128,4096]: add('auto','ordinary',52,slots=slots)
    for kind in ['scalar','latency']:
        add('auto','composition',52,kind,'sleef_ln_exp_scalar_fma',primitive='ln_exp')
        add('auto','composition',52,kind,'baseline',primitive='ln_exp',control=True,required=False)
    # Exact normalization is shared by log2/log10 and the ln_1p fallback.
    for backend in [b['name'] for b in builds]:
        for primitive in ['log2','log10']:
            for region in ['ordinary','wide','subnormal']:
                for kind in ['scalar','latency']:
                    add(backend,region,52,kind,'baseline',primitive=primitive,control=True,required=False)
        for region in ['ordinary','ln1p_fallback']:
            for kind,n in [('scalar',52),('vector',4096)]:
                add(backend,region,n,kind,'baseline',primitive='ln_1p',control=True,required=False)
    assert len({c['id'] for c in cells})==len(cells)
    return cells


def execution_groups(cells):
    """Qualify the observed x86 boundary cases before the rest of the matrix.

    Membership is declared before qualification; every cell still receives the
    same ten-process two-block test, and every required cell must pass.
    """
    def critical(c):
        if c['control'] or not c['required_parity'] or c['primitive'] != 'ln':
            return False
        backend, region, n, kind = c['backend'], c['population'], c['length'], c['kind']
        if backend == 'auto':
            if c['reference'] == 'core_math_ln':
                return region == 'wide' or (region == 'ordinary' and kind == 'latency')
            if kind == 'vector':
                if region in ['ordinary', 'wide']:
                    return n in [8, 16, 32, 33, 64, 65, 256, 4096]
                return n == 4096 and region in ['near_one', 'subnormal', 'mixed_positive']
        return kind == 'vector' and ((backend == 'avx512' and n in [16, 17] and region in ['ordinary', 'wide'])
                                     or (backend == 'avx2' and region == 'wide' and n == 13))
    first = [c['id'] for c in cells if critical(c)]
    rest = [c['id'] for c in cells if not critical(c)]
    return [first, rest] if first and rest else [[c['id'] for c in cells]]
