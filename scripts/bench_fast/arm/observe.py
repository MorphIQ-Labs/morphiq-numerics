import csv,json,math,struct
import mpmath as mp
import numpy as np
import matrix as M
E=M.E;P=M.P;mp.mp.prec=256
summary=[]
for f,name in [('exp','prod_exp'),('erfcx','prod_erfcx'),('cdf','prod_norm_cdf')]:
 words=sorted(set(b for bank,xs in M.BANKS.items() if bank.startswith(f+'-') for b in xs));xs=np.array([M.value(b) for b in words]);ys=E.evaluate(name,xs);zs=E.evaluate(name+'_slice',xs)
 failures=[];identities=[];worst=mp.mpf(0);sampled=0;fallback=0
 with (P/(f+'-bank-observations.csv')).open('w') as file:
  w=csv.writer(file);w.writerow(['input_bits','output_bits','slice_bits','accelerated','oracle_256bit','error','allowed','pass'])
  for word,x,y,z in zip(words,xs,ys,zs):
   yb=M.bits(y);zb=M.bits(z)
   if yb!=zb:identities.append(word)
   accelerated=M.active(f,x)
   if not math.isfinite(x):
    if math.isnan(x):ok=math.isnan(y) and yb==word
    elif f=='exp':ok=y==(math.inf if x>0 else 0.)
    elif f=='erfcx':ok=y==(0. if x>0 else math.inf)
    else:ok=y==(1. if x>0 else 0.)
    w.writerow([word,yb,zb,False,'special','n/a','owner special semantics',ok])
   else:
    a=mp.mpf(float(x));ref=mp.exp(a) if f=='exp' else mp.exp(a*a)*mp.erfc(a) if f=='erfcx' else mp.erfc(-a/mp.sqrt(2))/2
    if accelerated:
     error=abs(mp.mpf(float(y))-ref)/(1 if f=='cdf' else abs(ref));allowed=mp.mpf(2)**(-49 if f=='cdf' else -51);ok=error<=allowed;sampled+=1;worst=max(worst,error)
    else:
     fallback+=1
     if math.isinf(float(ref)):error=mp.mpf(0) if math.isinf(y) else mp.inf;allowed=mp.mpf(0);ok=error==0
     elif f=='exp':
      # Retained selected fallback points observed against correctly-rounded oracle;
      # no whole-domain guarantee is inferred from these finite observations.
      expected=float(ref);error=abs(mp.mpf(float(y))-ref);allowed='sampled rounded result';ok=M.bits(y)==M.bits(expected)
     elif f=='erfcx':
      error=abs(mp.mpf(float(y))-ref)
      relative=mp.mpf(2)**-53+(mp.mpf(2)**-122 if x<-.5 else mp.mpf(2)**-223 if x>=16 else 0)
      allowed=abs(ref)*relative+mp.mpf(2)**-1075+(mp.mpf(2)**-123 if -.5<=x<16 else 0);ok=error<=allowed
     else:
      error=abs(mp.mpf(float(y))-ref);allowed=abs(ref)*(mp.mpf(2)**-53+mp.mpf(2)**-111)+mp.mpf(2)**-1075;ok=error<=allowed
    if not ok:failures.append(word)
    w.writerow([word,yb,zb,accelerated,mp.nstr(ref,85),str(error),str(allowed),bool(ok)])
  # Exercise every declared public length with the exact materialized bank.
  for cell in M.CELLS:
   if cell['primitive']!=f or cell['mode']!='throughput':continue
   x=M.inputs(cell);a=E.evaluate(name,x);b=E.evaluate(name+'_slice',x)
   bad=np.flatnonzero(a.view('uint64')!=b.view('uint64'))
   identities.extend(dict(cell=cell['id'],index=int(i),input=M.bits(x[i])) for i in bad)
 summary.append(dict(primitive=f,unique_inputs=len(words),accelerated_cases=sampled,fallback_cases=fallback,max_accelerated_error=str(worst),failures=failures,scalar_slice_mismatches=identities))
(P/'bank-accuracy-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));assert not any(r['failures'] or r['scalar_slice_mismatches'] for r in summary)
