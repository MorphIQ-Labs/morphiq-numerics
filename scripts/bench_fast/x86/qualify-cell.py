"""One declared comparator cell per fresh process; no oracle/profile in timings."""
import argparse
import csv
import ctypes as C
import ctypes.util
import hashlib
import json
import math
import os
import platform
from pathlib import Path
import struct
import subprocess
import time

P = Path(__file__).resolve().parent
E = P / 'references'
D = C.POINTER(C.c_double)
KEEP = []
PAGE = 4096
# Every process, calibration included, places its buffers identically: the input
# on a page boundary, the output 2 KiB past one. Allocator state otherwise differs
# between processes, and kernel speed depends on the output's 4 KiB offset from
# its input (store-to-load aliasing; up to 1.8x on Sapphire Rapids, #243).
OUTPUT_PAGE_OFFSET = 2048


def cpu_frequencies(root=Path('/sys/devices/system/cpu')):
    """Read online CPUs only; offline cpufreq files can exist but reject reads."""
    frequency, offline = {}, []
    for cpu in sorted(root.glob('cpu[0-9]*')):
        online = cpu / 'online'
        state = online.read_text().strip() if online.exists() else '1'
        if state == '0':
            offline.append(cpu.name)
            continue
        if state != '1':
            raise ValueError(f'Invalid CPU online state at {online}: {state!r}')
        path = cpu / 'cpufreq/scaling_cur_freq'
        if path.exists():
            frequency[str(path)] = path.read_text().strip()
    return frequency, offline


def host():
    if platform.system() == 'Darwin':
        return dict(utc=time.time(), platform=platform.platform(),
                    affinity='macOS does not provide CPU affinity for this process',
                    cpuinfo=subprocess.check_output(['sysctl', '-a'], text=True, stderr=subprocess.DEVNULL),
                    power=subprocess.check_output(['pmset', '-g'], text=True))
    frequency, offline = cpu_frequencies()
    return dict(utc=time.time(), affinity=sorted(os.sched_getaffinity(0)),
                cpu_stat=Path('/proc/stat').read_text(),
                load=Path('/proc/loadavg').read_text(),
                cpuinfo=Path('/proc/cpuinfo').read_text(),
                frequency=frequency, offline_cpus=offline,
                thermal={str(p):p.read_text().strip() for p in Path('/sys/class/thermal').glob('thermal_zone*/temp')})


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
    ap.add_argument('--primitive', choices=['exp', 'erfcx', 'cdf', 'ln', 'ln_exp', 'log2', 'log10', 'ln_1p', 'log_cdf'], required=True)
    ap.add_argument('--length', type=int, required=True)
    ap.add_argument('--population', default='ordinary')
    ap.add_argument('--kind', choices=['vector', 'scalar', 'latency'], default='vector')
    ap.add_argument('--process', required=True)
    ap.add_argument('--counts', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--target-ms', type=int, default=600)
    ap.add_argument('--diagnostic', action='store_true')
    ap.add_argument('--balanced-stack', action='store_true')
    ap.add_argument('--symbol-prefix', default='prod_')
    ap.add_argument('--reference-product')
    args = ap.parse_args()
    if args.balanced_stack and (platform.machine() != 'x86_64' or args.cache_slots != 1 or args.kind == 'latency'):
        ap.error('Balanced stacks require native x86 independent scalar/packet timing with one cache slot')
    if platform.system() != 'Darwin':
        os.sched_setaffinity(0, {json.loads((P/'config.json').read_text())['cpu']})
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=False)
    native = C.CDLL(str(P/'bin/native-matrix.so'))
    if platform.system() == 'Darwin' and native.bench_set_qos() != 0:
        raise RuntimeError('Cannot establish USER_INITIATED QoS')
    for name in ['measure1', 'measure2', 'measure_packet', 'measure_chain1', 'measure_chain2']:
        method = getattr(native, name)
        method.argtypes = [C.c_void_p, D, D, C.c_size_t, C.c_uint64]
        method.restype = C.c_uint64
    symbol = dict(exp='exp', erfcx='erfcx', cdf='norm_cdf', ln='ln', ln_exp='ln_exp', log2='log2', log10='log10', ln_1p='ln_1p', log_cdf='log_norm_cdf')[args.primitive]
    symbol = args.symbol_prefix + symbol + ('_slice' if args.kind == 'vector' else '')
    product = pointer(Path(args.product), symbol)
    entries = {'ours': (product, 'measure_packet' if args.kind == 'vector' else 'measure1')}
    if args.reference_product:
        ref = pointer(Path(args.reference_product), symbol)
        method = 'measure_packet' if args.kind == 'vector' else 'measure1'
    elif args.reference.startswith('sleef_'):
        if args.reference in ['sleef_exp_scalar_fma', 'sleef_ln_scalar_fma', 'sleef_ln_scalar_purec']:
            library = E/('libsleef.3.9.0.dylib' if platform.system() == 'Darwin' else 'libsleef.so.3')
            function = 'Sleef_logd1_u10purec' if args.reference == 'sleef_ln_scalar_purec' else 'Sleef_logd1_u10purecfma' if args.primitive == 'ln' else 'Sleef_expd1_u10purecfma'
            ref = pointer(library, function)
            method = 'measure1'
        elif args.reference == 'sleef_ln_exp_scalar_fma':
            ref, method = C.cast(native.sleef_ln_exp_scalar_fma, C.c_void_p).value, 'measure1'
        else:
            ref = C.cast(getattr(native, args.reference), C.c_void_p).value
            method = 'measure_packet'
    elif args.reference == 'core_math_exp':
        ref, method = pointer(E/'libcoreexp.so', 'cr_exp'), 'measure1'
    elif args.reference == 'glibc_exp':
        if platform.system() != 'Linux' or platform.libc_ver()[0] != 'glibc':
            raise RuntimeError('glibc_exp requires native Linux with glibc')
        # Black-box ABI comparison only; no platform implementation source.
        library = ctypes.util.find_library('m')
        if library is None:
            raise RuntimeError('Cannot locate the system libm')
        ref, method = pointer(library, 'exp'), 'measure1'
    elif args.reference == 'core_math_ln':
        ref, method = pointer(E/('libcorelog.dylib' if platform.system() == 'Darwin' else 'libcorelog.so'), 'cr_log'), 'measure1'
    elif args.reference == 'libcerf_erfcx':
        ref, method = pointer(E/'libcerf.so', 'erfcx'), 'measure1'
    elif args.reference in ['scipy_ndtr', 'scipy_log_ndtr']:
        import scipy.special.cython_special as cy
        obj = cy.__pyx_capi__['__pyx_fuse_1ndtr' if args.reference == 'scipy_ndtr' else '__pyx_fuse_1log_ndtr']
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
    if args.reference == 'identical-binary':
        if not args.reference_product or product == ref:
            raise RuntimeError('Identical-binary control requires distinct loaded function addresses')
        if hashlib.sha256(Path(args.product).read_bytes()).digest() != hashlib.sha256(Path(args.reference_product).read_bytes()).digest():
            raise RuntimeError('Identical-binary control products differ')
    if args.kind == 'latency':
        entries = {key: (ptr, {'measure1': 'measure_chain1', 'measure2': 'measure_chain2'}[method])
                   for key, (ptr, method) in entries.items()}
    assert args.cache_slots > 0 and args.cache_slots & (args.cache_slots-1) == 0
    cache = C.CDLL(str(P/'bin/native-cache.so'))
    for name in ['measure1_cache', 'measure_packet_cache']:
        method = getattr(cache, name)
        method.argtypes = [C.c_void_p, D, D, C.c_size_t, C.c_uint64, C.c_size_t]
        method.restype = C.c_uint64
    for timer in [native, cache]:
        try:
            timer.bench_supported.argtypes = []
            timer.bench_supported.restype = C.c_int
            timer.bench_last_stack_address.argtypes = []
            timer.bench_last_stack_address.restype = C.c_size_t
        except AttributeError as error:
            raise RuntimeError('Rebuild native-matrix and native-cache with this harness version') from error
        if not timer.bench_supported():
            raise RuntimeError('Native x86 timers require an AVX-capable CPU and OS')
    stack_address = (cache if args.cache_slots > 1 else native).bench_last_stack_address
    values = inputs(args.primitive, args.population, args.length)
    words = values*args.cache_slots
    if platform.system() == 'Darwin':
        # The shared ln adapter also runs on native ARM. Preserve its existing
        # allocator placement; the x86 amendment does not qualify an ARM layout.
        x = (C.c_double * max(1, len(words)))(*words)
        y = (C.c_double * max(1, len(words)))()
        input_address, output_address = C.addressof(x), C.addressof(y)
    else:
        span = (max(1, len(words))*8 + PAGE - 1) // PAGE * PAGE
        arena = (C.c_byte * (2*span + 3*PAGE))()
        input_address = (C.addressof(arena) + PAGE - 1) // PAGE * PAGE
        output_address = input_address + span + OUTPUT_PAGE_OFFSET
        x, y = C.cast(input_address, D), C.cast(output_address, D)
        for index, value in enumerate(words):
            x[index] = value
    # SysV x86-64 call sites use 16-byte stack alignment. Cover every such
    # position modulo 4 KiB instead of sampling a few ASLR-selected positions.
    stack_offsets = list(range(0, PAGE, 16))
    stack_bases = {}
    measurement_id = 0
    chunks = None
    if args.balanced_stack:
        native.bench_set_inner_warmup.argtypes = [C.c_int]
        native.bench_set_inner_warmup.restype = None
        native.bench_set_inner_warmup(0)
        native.bench_with_stack.argtypes = [C.c_void_p, C.c_void_p, D, D,
                                            C.c_size_t, C.c_uint64, C.c_size_t]
        native.bench_with_stack.restype = C.c_uint64
        chunks = (out/'chunks.jsonl').open('x')

    def stack_sample(name, count, offset, kind, round_number, parent):
        ptr, method = entries[name]
        timer = C.cast(getattr(native, method), C.c_void_p).value
        if method not in stack_bases:
            # Placement probe performs zero numerical calls; it is not a sample.
            native.bench_with_stack(timer, ptr, x, y, args.length, 0, 0)
            stack_bases[method] = stack_address()
            if stack_bases[method] % 16:
                raise RuntimeError('Native timer stack is not ABI aligned')
        padding = (stack_bases[method]-offset) % PAGE
        start = time.monotonic_ns()
        elapsed = int(native.bench_with_stack(timer, ptr, x, y, args.length, count, padding))
        stop = time.monotonic_ns()
        actual = stack_address()
        row = dict(name=name, kind=kind, round=round_number, measurement_id=parent,
                   count=count, elapsed_ns=elapsed, stack_address=actual,
                   requested_stack_offset=offset, start_ns=start, stop_ns=stop)
        chunks.write(json.dumps(row)+'\n')
        chunks.flush()
        if actual % PAGE != offset:
            raise RuntimeError('Native stack placement changed; retain this invalid attempt')
        return row

    # The paired entries use exactly the same allocated input and output buffers.
    def measure(name, count):
        nonlocal measurement_id
        if args.balanced_stack:
            measurement_id += 1
            quotient, remainder = divmod(count, len(stack_offsets))
            return sum(stack_sample(name, quotient+(i < remainder), offset,
                                    'calibration', -1, measurement_id)['elapsed_ns']
                       for i, offset in enumerate(stack_offsets))
        ptr, method = entries[name]
        if args.cache_slots > 1:
            return int(getattr(cache, method+'_cache')(ptr, x, y, args.length, count, args.cache_slots))
        return int(getattr(native, method)(ptr, x, y, args.length, count))
    before = host()
    records = []
    def record(name, kind, count, round_number):
        elapsed = measure(name, count)
        row = dict(name=name, kind=kind, count=count, elapsed_ns=elapsed,
                   ns_per_call=elapsed/count, round=round_number, stack_address=stack_address())
        records.append(row)
        with (out/'samples.jsonl').open('a') as stream:
            stream.write(json.dumps(row)+'\n')
        return elapsed
    def record_calibration(name,kind,count,elapsed):
        row=dict(name=name,kind=kind,count=count,elapsed_ns=elapsed,ns_per_call=elapsed/count,round=0,stack_address=stack_address(),measurement_id=measurement_id)
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
            if args.balanced_stack:
                # Both the measured and half-count warmup cover every offset equally.
                quantum = 2*len(stack_offsets)
                counts[name] = (counts[name]+quantum-1)//quantum*quantum
        counts_path.write_text(json.dumps(counts, indent=2)+'\n')
    else:
        process = int(args.process)
        counts = json.loads(counts_path.read_text())
        if args.balanced_stack and any(count % (2*len(stack_offsets)) for count in counts.values()):
            raise ValueError('Balanced counts must be divisible by twice the number of stack positions')
        for round_number in range(2):
            if args.balanced_stack:
                aggregates = {(name, kind): dict(count=0, elapsed_ns=0)
                              for name in entries for kind in ['warmup', 'timed']}
                for index, offset in enumerate(stack_offsets):
                    order = list(entries)
                    if (process+round_number+index) % 2:
                        order.reverse()
                    for name in order:
                        for kind, count in [('warmup', counts[name]//2), ('timed', counts[name])]:
                            row = stack_sample(name, count//len(stack_offsets), offset,
                                               kind, round_number, round_number)
                            aggregate = aggregates[name, kind]
                            aggregate['count'] += row['count']
                            aggregate['elapsed_ns'] += row['elapsed_ns']
                for (name, kind), aggregate in aggregates.items():
                    row = dict(name=name, kind=kind, round=round_number, **aggregate,
                               ns_per_call=aggregate['elapsed_ns']/aggregate['count'],
                               chunks=len(stack_offsets), stack_address=None)
                    records.append(row)
                    with (out/'samples.jsonl').open('a') as stream:
                        stream.write(json.dumps(row)+'\n')
            else:
                order = list(entries)
                if (process+round_number) % 2:
                    order.reverse()
                for name in order:
                    record(name, 'warmup', max(1, counts[name]//2), round_number)
                    record(name, 'timed', counts[name], round_number)
    if chunks is not None:
        chunks.close()
    after = host()
    input_bytes = b''.join(struct.pack('>d', value) for value in values)
    metadata = dict(arguments=vars(args), counts=counts, before=before, after=after,
                    platform=platform.platform(), libc=platform.libc_ver(),
                    input_sha256=hashlib.sha256(input_bytes).hexdigest(),
                    product_sha256=hashlib.sha256(Path(args.product).read_bytes()).hexdigest(),
                    input_address=input_address, output_address=output_address,
                    call_addresses={name: ptr for name, (ptr, _) in entries.items()},
                    timer_addresses={name: C.cast(getattr(cache if args.cache_slots > 1 else native,
                        method+'_cache' if args.cache_slots > 1 else method), C.c_void_p).value
                        for name, (_, method) in entries.items()},
                    stack_placement=dict(policy='uniform-4KiB-interleaved' if args.balanced_stack else 'process-stack',
                                         offsets=stack_offsets if args.balanced_stack else None),
                    placement=dict(policy='allocator' if platform.system() == 'Darwin' else 'fixed-4KiB',
                                   input_page_offset=input_address % PAGE,
                                   output_minus_input_mod_page=(output_address-input_address) % PAGE))
    (out/'metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')
    timed = [r for r in records if r['kind']=='timed']
    if timed and not args.diagnostic and min(r['elapsed_ns'] for r in timed) < 250_000_000:
        raise SystemExit('Timed duration below 250 ms; retain this invalid attempt')


if __name__ == '__main__':
    main()
