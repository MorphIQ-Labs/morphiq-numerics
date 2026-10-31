import csv,json,math
import mpmath as mp
import numpy as np
import matrix as M
P=M.P;E=M.E;mp.mp.prec=256
summary=[]
for name,entry in E.entries.items():
 if name.startswith('prod_') or name=='composed_cdf_passes':continue
 f=entry['primitive'];rows=list(csv.DictReader((P/(f+'-bank-observations.csv')).open()));xs=[M.value(r['input_bits']) for r in rows];ys=E.evaluate(name,xs);worst=mp.mpf(0);witness=None;budget_exceeded=[];finite=0;special=[]
 with (P/(name+'-reference-observations.csv')).open('w') as file:
  w=csv.writer(file);w.writerow(['input_bits','reference_output_bits','oracle_256bit','accelerated','error','within_production_fast_budget'])
  for r,x,y in zip(rows,xs,ys):
   active=M.active(f,x)
   if r['oracle_256bit']=='special':
    special.append(dict(input=r['input_bits'],output=M.bits(y),production=r['output_bits'],same_bits=M.bits(y)==r['output_bits']));w.writerow([r['input_bits'],M.bits(y),'special',False,'n/a','n/a']);continue
   oracle=mp.mpf(r['oracle_256bit']);error=abs(mp.mpf(float(y))-oracle)/(1 if f=='cdf' else abs(oracle)) if math.isfinite(float(y)) else mp.mpf(0) if math.isinf(float(oracle)) else mp.inf
   within=None
   if active:
    finite+=1;within=error<=mp.mpf(2)**(-49 if f=='cdf' else -38 if f=='exp' else -51)
    if not within:budget_exceeded.append(r['input_bits'])
    if error>worst:worst=error;witness=r['input_bits']
   w.writerow([r['input_bits'],M.bits(y),r['oracle_256bit'],active,mp.nstr(error,30),within])
 summary.append(dict(name=name,primitive=f,accelerated_samples=finite,max_accelerated_error=str(worst),metric='absolute' if f=='cdf' else 'relative',worst_input=witness,production_fast_budget_exceeded=budget_exceeded,special_observations=special))
(P/'reference-accuracy-summary.json').write_text(json.dumps(dict(scope='Independent exact-bank observations for pinned practical references; sampled agreement does not establish their whole-domain bound or Numerics target/special-value guarantees',cells=summary),indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k not in ['special_observations','production_fast_budget_exceeded']}|dict(exceeded=len(r['production_fast_budget_exceeded'])) for r in summary],indent=2))
