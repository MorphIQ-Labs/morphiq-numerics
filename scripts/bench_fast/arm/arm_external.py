import ctypes as C
import csv
import json
import pathlib
import struct
import numpy as np
import scipy
import scipy.special.cython_special as cy

P = pathlib.Path(__file__).resolve().parent
D = C.POINTER(C.c_double)
LIBS = {k: C.CDLL(str(P/'bin'/v)) for k, v in {
    'native': 'libnativebench.dylib', 'core': 'libcoreexp.dylib',
    'cerf': 'libcerf.3.1.dylib', 'sleef': 'libsleef.3.9.0.dylib',
    'prod': 'libproduction_bench_wrapper.dylib'}.items()}
NATIVE = LIBS['native']
for name in ('measure1', 'measure2', 'measure_packet'):
    fn = getattr(NATIVE, name)
    fn.argtypes = [C.c_void_p, D, D, C.c_size_t, C.c_uint64]
    fn.restype = C.c_uint64
NATIVE.bench_set_qos.argtypes = []
NATIVE.bench_set_qos.restype = C.c_int
QOS_RESULT = NATIVE.bench_set_qos()
assert QOS_RESULT == 0, f'QoS request failed: {QOS_RESULT}'
entries = {}
def add(name, primitive, kind, lib, symbol):
    entries[name] = dict(name=name, primitive=primitive, kind=kind,
                         ptr=C.cast(getattr(LIBS[lib],symbol),C.c_void_p).value)
for primitive, symbol in [('exp','exp'), ('erfcx','erfcx'), ('cdf','norm_cdf')]:
    for suffix, kind in [('', 'scalar'), ('_slice', 'vector')]:
        name = 'prod_'+symbol+suffix
        add(name,primitive,kind,'prod',name)
add('core_math_exp','exp','scalar','core','cr_exp')
add('sleef_exp_scalar_fma','exp','scalar','sleef','Sleef_expd1_u10purecfma')
add('sleef_exp_neon','exp','vector','native','sleef_exp_neon')
add('libcerf_erfcx','erfcx','scalar','cerf','erfcx')
add('sleef_cdf_neon','cdf','vector','native','sleef_cdf_neon')
get_name = C.pythonapi.PyCapsule_GetName
get_name.argtypes = [C.py_object]; get_name.restype = C.c_char_p
get_pointer = C.pythonapi.PyCapsule_GetPointer
get_pointer.argtypes = [C.py_object,C.c_char_p]; get_pointer.restype = C.c_void_p
cap = cy.__pyx_capi__['__pyx_fuse_1ndtr']
signature = get_name(cap)
assert signature == b'double (double, int __pyx_skip_dispatch)', signature
entries['scipy_ndtr'] = dict(name='scipy_ndtr',primitive='cdf',kind='scalar_capsule',
                            ptr=get_pointer(cap,signature))
PAIRS = [('prod_exp','core_math_exp'), ('prod_exp','sleef_exp_scalar_fma'),
         ('prod_exp_slice','sleef_exp_neon'), ('prod_erfcx','libcerf_erfcx'),
         ('prod_erfcx_slice','libcerf_erfcx'), ('prod_norm_cdf','scipy_ndtr'),
         ('prod_norm_cdf_slice','sleef_cdf_neon')]
from inputs import ordinary_packets
PACKETS = {k: np.array(v,dtype=np.float64) for k,v in ordinary_packets().items()}
def evaluate(name, xs):
    r = entries[name]; x = np.ascontiguousarray(xs,dtype=np.float64); y = np.empty_like(x)
    if r['kind'] == 'vector':
        fn = C.CFUNCTYPE(None,D,D,C.c_size_t)(r['ptr'])
        fn(x.ctypes.data_as(D),y.ctypes.data_as(D),len(x))
    elif r['kind'] == 'scalar_capsule':
        fn = C.CFUNCTYPE(C.c_double,C.c_double,C.c_int)(r['ptr'])
        for i,v in enumerate(x): y[i] = fn(v,1)
    else:
        fn = C.CFUNCTYPE(C.c_double,C.c_double)(r['ptr'])
        for i,v in enumerate(x): y[i] = fn(v)
    return y
def measure(name,count):
    r=entries[name];x=PACKETS[r['primitive']];y=np.empty_like(x)
    method = NATIVE.measure_packet if r['kind']=='vector' else NATIVE.measure2 if r['kind']=='scalar_capsule' else NATIVE.measure1
    elapsed=method(r['ptr'],x.ctypes.data_as(D),y.ctypes.data_as(D),len(x),count)
    assert elapsed > 0 and np.isfinite(y).all()
    return elapsed
add('composed_cdf_passes','cdf','vector','native','composed_cdf_passes')
