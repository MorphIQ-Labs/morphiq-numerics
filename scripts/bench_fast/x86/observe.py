"""Independent observations and bit identity for every frozen timed input bank."""
from pathlib import Path
import ctypes as C, gzip, csv, hashlib, json, math, os, struct, sys
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.prec=256
D=C.POINTER(C.c_double);word=lambda x:struct.pack('>d',float(x)).hex();value=lambda w:struct.unpack('>d',bytes.fromhex(w))[0]
manifest=json.loads((P/'qualification-manifest.json').read_text());out=P/'qualification-observations';out.mkdir(exist_ok=False)
libs={name:C.CDLL(str(P/'qualification-bin'/f'{name}.so')) for name in ['auto','sse2','avx2','avx512']}
control=C.CDLL(str(P/'final-bin/control.so'));results=[]
for primitive,symbol in [('exp','exp'),('erfcx','erfcx'),('cdf','norm_cdf')]:
 paths=sorted({c['input']['file'] for c in manifest['cells'] if c['primitive']==primitive});banks={path:json.loads(Path(path).read_text()) for path in paths}
 words=sorted(set(w for bank in banks.values() for w in bank));xs={w:value(w) for w in words}
 functions={}
 for name,lib in libs.items():
  for prefix in ['prod_','control_']:
   scalar=getattr(lib,prefix+symbol);scalar.argtypes=[C.c_double];scalar.restype=C.c_double
   vector=getattr(lib,prefix+symbol+'_slice');vector.argtypes=[D,D,C.c_size_t];vector.restype=None
   functions[name,prefix]=scalar,vector
 old=getattr(control,'control_'+symbol);old.argtypes=[C.c_double];old.restype=C.c_double
 expected={w:word(functions['auto','prod_'][0](x)) for w,x in xs.items()};strong={w:word(old(x)) for w,x in xs.items()}
 mismatches=[];checks=0
 for (backend,prefix),(scalar,vector) in functions.items():
  reference=expected if prefix=='prod_' else strong
  for w,x in xs.items():
   actual=word(scalar(x));checks+=1
   if actual!=reference[w]:mismatches.append(dict(kind='scalar',backend=backend,prefix=prefix,input=w,actual=actual,expected=reference[w]))
  for path,bank in banks.items():
   x=(C.c_double*max(1,len(bank)))(*(xs[w] for w in bank));y=(C.c_double*max(1,len(bank)))();vector(x,y,len(bank))
   for w,actual in zip(bank,y):
    checks+=1
    if word(actual)!=reference[w]:mismatches.append(dict(kind='slice',backend=backend,prefix=prefix,bank=path,input=w,actual=word(actual),expected=reference[w]))
 budget=mp.mpf(2)**(-49 if primitive=='cdf' else -51);worst=mp.mpf(0);witness=None;failures=[];fallback_mismatches=[];observations=0
 active=lambda x:abs(x)<704 if primitive=='exp' else -.5<=x<16 and abs(x)>=2**-33 if primitive=='erfcx' else 2**-33<=abs(x)<=8
 def oracle(x):
  a=mp.mpf(x)
  return mp.exp(a) if primitive=='exp' else mp.exp(a*a)*mp.erfc(a) if primitive=='erfcx' else mp.erfc(-a/mp.sqrt(2))/2
 with gzip.open(out/(primitive+'.csv.gz'),'wt') as stream:
  writer=csv.writer(stream);writer.writerow(['input_bits','output_bits','reference_256bit','error'])
  for w,x in xs.items():
   if not active(x):
    if expected[w]!=strong[w]:fallback_mismatches.append(w)
    continue
   ref=oracle(x);y=mp.mpf(value(expected[w]));error=abs(y-ref)/(1 if primitive=='cdf' else abs(ref));observations+=1
   writer.writerow([w,expected[w],mp.nstr(ref,85),mp.nstr(error,30)])
   if error>worst:worst=error;witness=w
   if error>budget:failures.append(w)
 with mp.workprec(512):
  ref512=oracle(xs[witness]);error512=abs(mp.mpf(value(expected[witness]))-ref512)/(1 if primitive=='cdf' else abs(ref512))
 row=dict(primitive=primitive,unique_inputs=len(words),banks=len(banks),identity_checks=checks,mismatches=mismatches,fallback_mismatches=fallback_mismatches,observations=observations,budget=float(budget),max_error=float(worst),witness=witness,witness_error_512bit=mp.nstr(error512,50),failures=failures)
 results.append(row);(out/'summary.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(row),flush=True)
assert not any(r['mismatches'] or r['fallback_mismatches'] or r['failures'] for r in results)
