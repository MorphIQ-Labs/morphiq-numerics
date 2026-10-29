import csv,json,math,statistics
from scipy.stats import t
import matrix as M
P=M.P;result=[];missing=[]
for c in M.CELLS:
 samples=[];base=P/'qualified'/c['id']
 for process in range(10):
  f=base/str(process)/'samples.csv'
  if not f.exists():break
  samples += [r for r in csv.DictReader(f.open()) if r['kind']=='timed']
 if len(samples)!=40:missing.append(c['id']);continue
 logs=[];times={n:[] for n in c['pair']}
 for process in range(10):
  rounds=[]
  for rep in range(2):
   d={r['name']:float(r['ns_per_call']) for r in samples if int(r['process'])==process and int(r['round'])==rep};assert set(d)==set(c['pair']);rounds.append(math.log(d[c['pair'][0]]/d[c['pair'][1]]))
  logs.append(statistics.median(rounds))
  for name in c['pair']:times[name].append(statistics.median(float(r['ns_per_call']) for r in samples if r['name']==name and int(r['process'])==process))
 mean=statistics.mean(logs);upper=math.exp(mean+t.ppf(.95,9)*statistics.stdev(logs)/math.sqrt(10));minimum=min(int(r['elapsed_ns']) for r in samples)
 result.append(dict(**c,ratio=math.exp(mean),upper95=upper,meets_cost=upper<=1,duration_pass=minimum>=250000000,minimum_ns=minimum,process_log_ratios=logs,times={n:dict(median_ns=statistics.median(v),process_medians=v,range_fraction=(max(v)-min(v))/statistics.median(v),block_drift=abs(statistics.median(v[5:])/statistics.median(v[:5])-1)) for n,v in times.items()}))
summary=dict(source=(P/'source.json').read_text() if (P/'source.json').exists() else None,complete=len(result)==len(M.CELLS),completed_cells=len(result),missing=missing,required_failed=[r['id'] for r in result if r['parity_required'] and not r['meets_cost']],duration_failed=[r['id'] for r in result if not r['duration_pass']],cells=result)
(P/'qualification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('complete',summary['complete'],'cells',len(result),'cost failures',summary['required_failed'],'duration failures',summary['duration_failed'])
