"""Freeze native input bits and the already-declared x86 comparison cells."""
from pathlib import Path
import csv, hashlib, json, math, struct
import mpmath as mp
P=Path(__file__).resolve().parent
mp.mp.prec=256
banks=P/'qualification-inputs';banks.mkdir(exist_ok=False)
bits=lambda x:struct.pack('>d',float(x)).hex()
value=lambda w:struct.unpack('>d',bytes.fromhex(w))[0]
from inputs import ordinary_packets
ordinary={f:[bits(x) for x in xs] for f,xs in ordinary_packets().items()}
active=lambda f,x: abs(x)<704 if f=='exp' else -.5<=x<16 and abs(x)>=2**-33 if f=='erfcx' else 2**-33<=abs(x)<=8
boundaries={}
# Rounded reduction ties, neighboring representable values, and domain endpoints.
seeds=[float((mp.mpf(n)+mp.mpf('.5'))*mp.log(2)/512) for n in range(-520000,520001,8191)]
seeds += [float((mp.mpf(n)+mp.mpf('.5'))*mp.log(2)/1024) for n in range(-1040000,1040001,16381)]
seeds += [-math.nextafter(704.,0.),math.nextafter(704.,0.),0.,-0.,2**-1022,-2**-1022,2**-1074,-2**-1074,2**-54,-2**-54]
boundaries['exp']=[bits(y) for x in seeds for y in [math.nextafter(x,-math.inf),x,math.nextafter(x,math.inf)] if active('exp',y)]
seeds=[(k+.5)/32 for k in range(-16,32)] + [2**e*(1+i/32) for e in range(4) for i in range(33)] + [-.5,-2**-33,2**-33]
boundaries['erfcx']=[bits(y) for x in seeds for y in [math.nextafter(x,-math.inf),x,math.nextafter(x,math.inf)] if active('erfcx',y)]
seeds=[-8.,-1.,-2**-33,2**-33,1.,8.]
boundaries['cdf']=[bits(y) for x in seeds for y in [math.nextafter(x,-math.inf),x,math.nextafter(x,math.inf)] if active('cdf',y)]
extra={}
for f in ordinary:
 extra[f,'boundary']=boundaries[f]
 lo,hi={'exp':(-703.999,-680.),'erfcx':(12.,15.999),'cdf':(-8.,-7.)}[f]
 extra[f,'tail']=[bits(lo+(hi-lo)*(i+.5)/52) for i in range(52)]
 if f=='cdf':extra[f,'cancellation']=[bits((-1 if i%2 else 1)*2**(-33+32*i/51)) for i in range(52)]
 special={'exp':[-745.,-710.,-704.,704.,710.,float('inf'),-float('inf'),float('nan')], 'erfcx':[-1.,-.5001,16.,27.,0.,float('inf'),-float('inf'),float('nan')], 'cdf':[-9.,9.,-2**-34,2**-34,0.,float('inf'),-float('inf'),float('nan')]}[f]
 extra[f,'mixed']=[bits(special[(i//8)%len(special)]) if i%8==0 else ordinary[f][i%52] for i in range(64)]
 extra[f,'fallback']=[bits(x) for x in special]
entries={};cells=[]
def bank(f,pop,n):
 key=f'{f}-{pop}-{n}'
 if key not in entries:
  if pop=='wide':
   lo,hi={'exp':(-703.999,703.999),'erfcx':(-.5,15.999),'cdf':(-8.,8.)}[f]
   words=[bits(lo+(hi-lo)*(i+.5)/n) for i in range(n)]
   # Do not manufacture a strong fallback in a named accelerated-domain cell.
   words=[bits(2**-33) if not active(f,value(w)) else w for w in words]
  else:
   source=ordinary[f] if pop=='ordinary' else extra[f,pop]
   words=[source[i%len(source)] for i in range(n)]
  path=banks/(key+'.json');path.write_text(json.dumps(words)+'\n')
  count=sum(not active(f,value(w)) for w in words)
  entries[key]=dict(file=str(path),length=n,sha256=hashlib.sha256(b''.join(bytes.fromhex(w) for w in words)).hexdigest(),strong_fallbacks=count)
 return entries[key]
def ref_for(f,backend,n):
 if f=='erfcx':return 'libcerf_erfcx'
 width=backend
 if backend=='auto':width='avx512' if f=='cdf' or n>=8 else 'avx2' if n>=4 else 'sse2'
 # exp chooses smaller packets in each supported static build for short slices.
 if f=='exp':
  if n<4:width='sse2'
  elif n<8 and width=='avx512':width='avx2'
 return f'sleef_{f}_{width}'
def add(f,backend,n,pop,kind='vector',ref=None,control=False):
 b=bank(f,pop,n);ref=ref or ref_for(f,backend,n)
 key=f'{backend}-{f}-{kind}-{ref}-{pop}-{n}'
 cells.append(dict(id=key,primitive=f,backend=backend,length=n,population=pop,kind=kind,reference=ref,input=b,product=str(P/'qualification-bin'/f'{backend}.so'),required_parity=n>0 and b['strong_fallbacks']==0 and not control,control=control))
lengths=list(range(18))+[31,32,33,51,52,53,63,64,65,256,4096,65536]
for f in ordinary:
 for n in lengths:
  for pop in ['ordinary','wide']:add(f,'auto',n,pop)
for backend in ['sse2','avx2','avx512']:
 for f in ['exp','cdf']:
  for n in list(range(1,18))+[52,4096,65536]:
   for pop in ['ordinary','wide']:add(f,backend,n,pop)
 for n in [52,4096]:
  for pop in ['ordinary','wide']:add('erfcx',backend,n,pop)
for f in ordinary:
 for pop in ['boundary','tail','mixed','fallback']+(['cancellation'] if f=='cdf' else []):
  for n in [52,4096]:add(f,'auto',n,pop)
 for ref in {'exp':['core_math_exp','sleef_exp_scalar_fma'],'erfcx':['libcerf_erfcx'],'cdf':['scipy_ndtr']}[f]:
  for pop in ['ordinary','wide']:
   for n in [52,4096]:add(f,'auto',n,pop,'scalar',ref)
   add(f,'auto',52,pop,'latency',ref)
 for kind in ['scalar','vector']:
  for n in [52,4096]:add(f,'auto',n,'ordinary',kind,'strong-control',True)
for f in ordinary:
 for slots in [128,4096]:
  add(f,'auto',52,'ordinary')
  cells[-1]['id']+=f'-cache-{slots}'
  cells[-1]['cache_slots']=slots
manifest=dict(status='Frozen inputs and declared cells; no qualification result yet',cells=cells,builds=json.loads((P/'qualification-builds.json').read_text()),protocol=dict(processes=10,blocks=2,paired_rounds_per_process=2,target_ms=600,minimum_ms=250,upper95_t9=1.8331129326536335,maximum_upper_ratio=1.0,absolute_spread_gate='retired'))
(P/'qualification-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(cells),'cells;',sum(c['required_parity'] for c in cells),'required parity cells;',len(entries),'input banks')
