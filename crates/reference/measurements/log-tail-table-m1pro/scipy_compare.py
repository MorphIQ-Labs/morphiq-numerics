import ctypes as c, struct, time, sys
import numpy as np
import scipy
import scipy.special as sp
import scipy.special.cython_special as cy
lib=c.CDLL(sys.argv[1])
lib.measure.argtypes=[c.c_void_p,c.POINTER(c.c_double),c.c_size_t,c.c_int]
lib.measure.restype=c.c_double
ptr=c.pythonapi.PyCapsule_GetPointer
ptr.argtypes=[c.py_object,c.c_char_p];ptr.restype=c.c_void_p
fn=ptr(cy.__pyx_capi__['__pyx_fuse_1log_ndtr'],b'double (double, int __pyx_skip_dispatch)')
def workload(kind):
    xs=[]
    for i in range(1024):
        u=i/1023.0
        if kind=='negative_far_tail': x=-37.0-u
        elif kind=='negative_first_table': x=-37.0-27.0*u
        elif kind=='negative_tail': x=-8.0-28.0*u
        elif kind=='negative_wide_tail':
            e=6+i*506//1023
            fraction=(i*0x9e3779b97f4a7c15)&((1<<50)-1)
            x=-struct.unpack('d',struct.pack('Q',((e+1023)<<52)|fraction))[0]
        else: raise ValueError(kind)
        xs.append(x)
    return np.array(xs,dtype=np.float64)
print('function,workload,count,scalar_ns,batch_ns,scalar_chain_ns,nonfinite')
for kind in ['negative_far_tail','negative_first_table']:
    xs=workload(kind); out=np.empty_like(xs)
    scalar=lib.measure(fn,xs.ctypes.data_as(c.POINTER(c.c_double)),len(xs),0)
    chain=lib.measure(fn,xs.ctypes.data_as(c.POINTER(c.c_double)),len(xs),1)
    start=time.perf_counter_ns(); rounds=0
    while time.perf_counter_ns()-start<150_000_000:
        sp.log_ndtr(xs,out=out);rounds+=1
    batch=(time.perf_counter_ns()-start)/(rounds*len(xs))
    print(f'scipy_{scipy.__version__},{kind},{len(xs)},{scalar:.3f},{batch:.3f},{chain:.3f},{np.count_nonzero(~np.isfinite(out))}')
