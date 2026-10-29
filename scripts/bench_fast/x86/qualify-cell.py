"""One declared comparator cell per fresh process; no oracle/profile in timings."""
import argparse
import csv
import ctypes as C
import hashlib
import json
import math
import os
from pathlib import Path
import struct
import time

P = Path(__file__).resolve().parent
E = P / 'references'
D = C.POINTER(C.c_double)
KEEP = []


def host():
    return dict(utc=time.time(), affinity=sorted(os.sched_getaffinity(0)),
                cpu_stat=Path('/proc/stat').read_text(),
                load=Path('/proc/loadavg').read_text(),
                cpuinfo=Path('/proc/cpuinfo').read_text())


def pointer(path, symbol):
    lib = C.CDLL(str(path))
    KEEP.append(lib)
    return C.cast(getattr(lib, symbol), C.c_void_p).value


def inputs(primitive, population, length):
    if primitive == 'ln' and population in ['ordinary', 'wide']:
        if population == 'ordinary':
            return [.5 + 1.5*(i % 52)/51 for i in range(length)]
        # Positive normal encodings spanning every exponent, with exact fractions.
        return [struct.unpack('>d', struct.pack('>Q',
            ((1 + i % 2046) << 52) | ((i * 0x9e3779b97f4a7c15) & ((1 << 52)-1))))[0]
            for i in range(length)]
    if population == 'ordinary':
        from inputs import ordinary_packets
        words=ordinary_packets()[primitive]
        return [words[i % len(words)] for i in range(length)]
    if population == 'wide':
        lo, hi = dict(exp=(-703.999, 703.999), erfcx=(-.5, 15.999), cdf=(-8, 8))[primitive]
        return [lo + (hi-lo)*(i+.5)/length for i in range(length)]
    data = json.loads(Path(population).read_text())
    return [struct.unpack('>d', bytes.fromhex(data[i % len(data)]))[0] for i in range(length)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache-slots', type=int, default=1)
    ap.add_argument('--product', required=True)
    ap.add_argument('--reference', required=True)
    ap.add_argument('--primitive', choices=['exp', 'erfcx', 'cdf', 'ln'], required=True)
    ap.add_argument('--length', type=int, required=True)
    ap.add_argument('--population', default='ordinary')
    ap.add_argument('--kind', choices=['vector', 'scalar', 'latency'], default='vector')
    ap.add_argument('--process', required=True)
    ap.add_argument('--counts', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--target-ms', type=int, default=600)
    ap.add_argument('--diagnostic', action='store_true')
    ap.add_argument('--symbol-prefix', default='prod_')
    ap.add_argument('--reference-product')
    args = ap.parse_args()
    os.sched_setaffinity(0, {json.loads((P/'config.json').read_text())['cpu']})
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=False)
    native = C.CDLL(str(P/'bin/native-matrix.so'))
    for name in ['measure1', 'measure2', 'measure_packet', 'measure_chain1', 'measure_chain2']:
        method = getattr(native, name)
        method.argtypes = [C.c_void_p, D, D, C.c_size_t, C.c_uint64]
        method.restype = C.c_uint64
    symbol = dict(exp='exp', erfcx='erfcx', cdf='norm_cdf', ln='ln')[args.primitive]
    symbol = args.symbol_prefix + symbol + ('_slice' if args.kind == 'vector' else '')
    product = pointer(Path(args.product), symbol)
    entries = {'ours': (product, 'measure_packet' if args.kind == 'vector' else 'measure1')}
    if args.reference_product:
        ref = pointer(Path(args.reference_product), symbol)
        method = 'measure_packet' if args.kind == 'vector' else 'measure1'
    elif args.reference.startswith('sleef_'):
        if args.reference in ['sleef_exp_scalar_fma', 'sleef_ln_scalar_fma']:
            ref = pointer(E/'libsleef.so.3', 'Sleef_logd1_u10purecfma' if args.primitive == 'ln' else 'Sleef_expd1_u10purecfma')
            method = 'measure1'
        else:
            ref = C.cast(getattr(native, args.reference), C.c_void_p).value
            method = 'measure_packet'
    elif args.reference == 'core_math_exp':
        ref, method = pointer(E/'libcoreexp.so', 'cr_exp'), 'measure1'
    elif args.reference == 'libcerf_erfcx':
        ref, method = pointer(E/'libcerf.so', 'erfcx'), 'measure1'
    elif args.reference == 'scipy_ndtr':
        import scipy.special.cython_special as cy
        obj = cy.__pyx_capi__['__pyx_fuse_1ndtr']
        name = C.pythonapi.PyCapsule_GetName
        name.argtypes, name.restype = [C.py_object], C.c_char_p
        get = C.pythonapi.PyCapsule_GetPointer
        get.argtypes, get.restype = [C.py_object, C.c_char_p], C.c_void_p
        signature = name(obj)
        assert signature == b'double (double, int __pyx_skip_dispatch)'
        ref, method = get(obj, signature), 'measure2'
    else:
        raise ValueError(args.reference)
    entries['reference'] = ref, method
    if args.kind == 'latency':
        entries = {key: (ptr, {'measure1': 'measure_chain1', 'measure2': 'measure_chain2'}[method])
                   for key, (ptr, method) in entries.items()}
    assert args.cache_slots > 0 and args.cache_slots & (args.cache_slots-1) == 0
    cache = C.CDLL(str(P/'bin/native-cache.so'))
    for name in ['measure1_cache', 'measure_packet_cache']:
        method = getattr(cache, name)
        method.argtypes = [C.c_void_p, D, D, C.c_size_t, C.c_uint64, C.c_size_t]
        method.restype = C.c_uint64
    values = inputs(args.primitive, args.population, args.length)
    x = (C.c_double * max(1, args.length*args.cache_slots))(*(values*args.cache_slots))
    y = (C.c_double * max(1, args.length*args.cache_slots))()
    # The paired entries use exactly the same allocated input and output buffers.
    def measure(name, count):
        ptr, method = entries[name]
        if args.cache_slots > 1:
            return int(getattr(cache, method+'_cache')(ptr, x, y, args.length, count, args.cache_slots))
        return int(getattr(native, method)(ptr, x, y, args.length, count))
    before = host()
    records = []
    def record(name, kind, count, round_number):
        elapsed = measure(name, count)
        row = dict(name=name, kind=kind, count=count, elapsed_ns=elapsed,
                   ns_per_call=elapsed/count, round=round_number)
        records.append(row)
        with (out/'samples.jsonl').open('a') as stream:
            stream.write(json.dumps(row)+'\n')
        return elapsed
    def record_calibration(name,kind,count,elapsed):
        row=dict(name=name,kind=kind,count=count,elapsed_ns=elapsed,ns_per_call=elapsed/count,round=0)
        with (out/'samples.jsonl').open('a') as stream:stream.write(json.dumps(row)+'\n')
    counts_path = Path(args.counts)
    if args.process == 'calibration':
        assert not counts_path.exists()
        from protocol import calibrate
        counts = {}
        for name in entries:
            counts[name] = calibrate(lambda count:measure(name,count),
                lambda kind,count,elapsed:record_calibration(name,kind,count,elapsed),
                target_ns=args.target_ms*1_000_000)
        counts_path.write_text(json.dumps(counts, indent=2)+'\n')
    else:
        process = int(args.process)
        counts = json.loads(counts_path.read_text())
        for round_number in range(2):
            order = list(entries)
            if (process+round_number) % 2:
                order.reverse()
            for name in order:
                record(name, 'warmup', max(1, counts[name]//2), round_number)
                record(name, 'timed', counts[name], round_number)
    after = host()
    input_bytes = b''.join(struct.pack('>d', value) for value in values)
    metadata = dict(arguments=vars(args), counts=counts, before=before, after=after,
                    input_sha256=hashlib.sha256(input_bytes).hexdigest(),
                    product_sha256=hashlib.sha256(Path(args.product).read_bytes()).hexdigest(),
                    input_address=C.addressof(x), output_address=C.addressof(y))
    (out/'metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')
    timed = [r for r in records if r['kind']=='timed']
    if timed and not args.diagnostic and min(r['elapsed_ns'] for r in timed) < 250_000_000:
        raise SystemExit('Timed duration below 250 ms; retain this invalid attempt')


if __name__ == '__main__':
    main()
