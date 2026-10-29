import ctypes as C,hashlib,json,math,pathlib,struct
import numpy as np
import arm_external as E
P=pathlib.Path(__file__).resolve().parent
D=E.D;N=E.NATIVE
for name in ['measure_chain1','measure_chain2']:
 fn=getattr(N,name);fn.argtypes=[C.c_void_p,D,D,C.c_size_t,C.c_uint64];fn.restype=C.c_uint64
for name in ['measure_cache1','measure_cache_packet']:
 fn=getattr(N,name);fn.argtypes=[C.c_void_p,D,D,C.c_size_t,C.c_uint64,D,C.c_size_t];fn.restype=C.c_uint64
def bits(v):return struct.pack('>d',float(v)).hex()
def value(b):return struct.unpack('>d',bytes.fromhex(b))[0]
def active(f,x):return abs(x)<704 if f=='exp' else -.5<=x<16 and abs(x)>=2**-33 if f=='erfcx' else 2**-33<=abs(x)<=8
def make_banks():
 import mpmath as mp
 mp.mp.prec=256
 banks={}
 for f,lo,hi in [('exp',-703.99,703.99),('erfcx',-.499999,15.99999),('cdf',-8.,8.)]:
  ordinary=list(E.PACKETS[f]);wide=[lo+(hi-lo)*i/1023 for i in range(1024)]
  if f=='exp':points=[float((mp.mpf(n)+offset)*mp.log(2)/1024) for n in range(-1038000,1038001,1009) for offset in [mp.mpf(0),mp.mpf('.5')]]+[-704.,704.,0.]
  elif f=='erfcx':points=[(i+.5)/32 for i in range(-16,32)]+[2.**e*(1+i/32) for e in range(4) for i in range(33)]+[-.5,1.,-2**-33,2**-33,16.]
  else:points=[-8.,-1.,-2**-33,2**-33,1.,8.]+[-8+i/64 for i in range(1025)]
  boundary=[z for x in points for z in [math.nextafter(x,-math.inf),x,math.nextafter(x,math.inf)] if active(f,z)]
  if f=='exp':tail=[sign*(690+13.99*i/511) for i in range(512) for sign in [-1,1]];fallback=[-746.,-745.,-744.,-710.,-704.,704.,708.,709.,710.]
  elif f=='erfcx':tail=[10+5.99999*i/1023 for i in range(1024)];fallback=[-27.,-20.,-5.,-1.,-.50001,-2**-34,0.,2**-34,16.,20.,27.,100.]
  else:tail=[sign*(6+2*i/511) for i in range(512) for sign in [-1,1]];fallback=[-38.,-12.,-9.,-2**-34,0.,2**-34,9.,12.,38.]
  special=[0.,-0.,math.inf,-math.inf,value('7ff8123456789abc'),value('fff8123456789abc')]
  mixed=[fallback[(i//8)%len(fallback)] if i%8==7 else ordinary[i%len(ordinary)] for i in range(416)]
  for label,xs in [('ordinary',ordinary),('wide',wide),('boundary',boundary),('tails',tail),('mixed',mixed),('fallback',fallback),('special',special)]:banks[f+'-'+label]=[bits(x) for x in xs]
 return banks
def make_cells():
 cells=[]
 def add(f,label,n,pair,mode='throughput',gate=True):
  cells.append(dict(id=f'{len(cells):03d}',primitive=f,bank=f+'-'+label,length=n,pair=list(pair),mode=mode,parity_required=gate,reason='comparable fast cost' if gate else 'empty/strong fallback/special/cache diagnostic; unmatched guarantees or instrumentation'))
 scalar=[('exp',('prod_exp','core_math_exp')),('exp',('prod_exp','sleef_exp_scalar_fma')),('erfcx',('prod_erfcx','libcerf_erfcx')),('cdf',('prod_norm_cdf','scipy_ndtr'))]
 slices=[('exp',('prod_exp_slice','sleef_exp_neon')),('erfcx',('prod_erfcx_slice','libcerf_erfcx')),('cdf',('prod_norm_cdf_slice','sleef_cdf_neon'))]
 lengths=list(range(18))+[31,32,33,51,52,53,63,64,65,256,4096,65536]
 for f,pair in slices:
  for n in lengths:add(f,'ordinary',n,pair,gate=n>0)
 for f,pair in scalar:
  for label in ['ordinary','wide','boundary','tails','mixed','fallback','special']:add(f,label,52,pair,gate=label not in ['mixed','fallback','special'])
 for f,pair in slices:
  for label in ['wide','boundary','tails','mixed','fallback','special']:
   for n in [52,4096]:add(f,label,n,pair,gate=label not in ['mixed','fallback','special'])
 for f,pair in scalar:add(f,'ordinary',52,pair,mode='latency')
 for f,pair in slices:add(f,'ordinary',52,pair,mode='cache',gate=False)
 for n in [52,4096]:
  add('cdf','tails',n,('prod_norm_cdf_slice','composed_cdf_passes'),gate=False)
  cells[-1]['reason']='Same propagated 2^-49 CDF budget; synthetic multi-pass composition cost diagnostic, not a separate consumer qualification'
 return cells
BANKS=json.loads((P/'banks.json').read_text()) if (P/'banks.json').exists() else {}
CELLS=json.loads((P/'cells.json').read_text()) if (P/'cells.json').exists() else []
def inputs(cell):
 b=BANKS[cell['bank']];return np.array([value(b[i%len(b)]) for i in range(cell['length'])],dtype=np.float64)
def measure(cell,name,count):
 r=E.entries[name];x=inputs(cell);y=np.zeros(max(1,len(x)),dtype=np.float64)
 if cell['mode']=='latency':fn=N.measure_chain2 if r['kind']=='scalar_capsule' else N.measure_chain1
 elif cell['mode']=='cache':fn=N.measure_cache_packet if r['kind']=='vector' else N.measure_cache1
 else:fn=N.measure_packet if r['kind']=='vector' else N.measure2 if r['kind']=='scalar_capsule' else N.measure1
 args=[r['ptr'],x.ctypes.data_as(D),y.ctypes.data_as(D),len(x),count]
 if cell['mode']=='cache':
  cache=np.ones(65536,dtype=np.float64);args += [cache.ctypes.data_as(D),len(cache)]
 elapsed=fn(*args);assert elapsed>0
 return elapsed
if __name__=='__main__':
 assert not BANKS and not CELLS,'Frozen manifests already exist'
 (P/'banks.json').write_text(json.dumps(make_banks(),indent=2)+'\n');(P/'cells.json').write_text(json.dumps(make_cells(),indent=2)+'\n')
 print('Cells',len(make_cells()),'required',sum(c['parity_required'] for c in make_cells()))
