import csv,ctypes as C,json,math,pathlib,subprocess
import mpmath as mp
import numpy as np
import matrix as M
P=M.P;E=M.E;D=E.D;mp.mp.prec=256
lib=C.CDLL(str(P/'allocation-build/release/liballocation_observation_wrapper.dylib'))
probe=lib.observe_allocations;probe.argtypes=[C.c_uint32,D,D,C.c_size_t];probe.restype=C.c_uint64
allocation=[];fallback=[];composition=[]
for mode,(f,name) in enumerate([('exp','prod_exp'),('erfcx','prod_erfcx'),('cdf','prod_norm_cdf')]):
 strong=getattr(lib,'strong_'+f);strong.argtypes=[C.c_double];strong.restype=C.c_double
 for bank,words in M.BANKS.items():
  if not bank.startswith(f+'-'):continue
  for word in words:
   x=M.value(word)
   if not M.active(f,x):
    y=E.evaluate(name,[x])[0];z=strong(x);fallback.append(dict(primitive=f,bank=bank,input=word,fast=M.bits(y),strong=M.bits(z),equal=M.bits(y)==M.bits(z)))
 for c in M.CELLS:
  if c['primitive']!=f or c['mode']!='throughput':continue
  x=M.inputs(c);y=np.zeros(len(x));count=probe(mode,x.ctypes.data_as(D),y.ctypes.data_as(D),len(x));expected=E.evaluate(name+'_slice',x)
  allocation.append(dict(cell=c['id'],length=len(x),allocations=count,output_matches_uninstrumented=bool((y.view('uint64')==expected.view('uint64')).all())))
for c in M.CELLS:
 if c['pair'][1]!='composed_cdf_passes':continue
 x=M.inputs(c);a=E.evaluate(c['pair'][0],x);b=E.evaluate(c['pair'][1],x);worst=mp.mpf(0)
 for xx,yy in zip(x,b):
  ref=mp.erfc(-mp.mpf(float(xx))/mp.sqrt(2))/2;worst=max(worst,abs(mp.mpf(float(yy))-ref))
 composition.append(dict(cell=c['id'],length=len(x),max_absolute_error=str(worst),bound=str(mp.mpf(2)**-49),bound_pass=bool(worst<=mp.mpf(2)**-49),bit_identical_to_public_fused=bool((a.view('uint64')==b.view('uint64')).all()),scratch_bytes=16*len(x),scratch_storage='C stack VLA, no initialization or heap allocation',passes='one argument-building pass, exp slice pass, erfcx slice pass, final-product pass'))
# Independently observe the feedback chain actually timed, separately for each native scalar entry.
latency=[]
for cell in M.CELLS:
 if cell['mode']!='latency':continue
 f=cell['primitive'];base=M.inputs(cell)
 for name in cell['pair']:
  r=E.entries[name];fn=C.CFUNCTYPE(C.c_double,C.c_double,C.c_int)(r['ptr']) if r['kind']=='scalar_capsule' else C.CFUNCTYPE(C.c_double,C.c_double)(r['ptr'])
  v=0.;worst=mp.mpf(0);inputs=[];fails=[]
  for i in range(20*len(base)):
   x=float(base[i%len(base)]+v*0.03125);v=fn(x,1) if r['kind']=='scalar_capsule' else fn(x);inputs.append(M.bits(x))
   z=mp.mpf(x);ref=mp.exp(z) if f=='exp' else mp.exp(z*z)*mp.erfc(z) if f=='erfcx' else mp.erfc(-z/mp.sqrt(2))/2
   err=abs(mp.mpf(v)-ref)/(1 if f=='cdf' else abs(ref));worst=max(worst,err)
   if name.startswith('prod_') and err>mp.mpf(2)**(-49 if f=='cdf' else -51):fails.append(M.bits(x))
  latency.append(dict(cell=cell['id'],name=name,observations=len(inputs),input_bits=inputs,max_error=str(worst),production_failures=fails))
result=dict(allocations=allocation,fallback_identity=fallback,composition=composition,latency_oracle=latency,limitations='Allocation instrumentation is separate from uninstrumented timing; observed Rust heap allocation calls only. Scratch buffers and Python/C input construction are outside primitive timing except explicitly measured composition/cache work. Feedback timing includes multiplication/addition and indirect call overhead; native assembly confirms the loop-carried dependency.')
(P/'diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
with (P/'footprint.txt').open('w') as out:
 for args in [['size','-m',str(P/'bin/libproduction_bench_wrapper.dylib')],['nm','-n',str(P/'bin/libproduction_bench_wrapper.dylib')]]:
  out.write(' '.join(args)+'\n');p=subprocess.run(args,text=True,capture_output=True);out.write(p.stdout+p.stderr)
assert all(r['allocations']==0 and r['output_matches_uninstrumented'] for r in allocation)
assert all(r['equal'] for r in fallback)
assert all(r['bound_pass'] and r['bit_identical_to_public_fused'] for r in composition)
assert all(not r['production_failures'] for r in latency)
print('Allocation cases',len(allocation),'all zero; fallback identity',len(fallback),'passed; composition and latency oracle passed')
