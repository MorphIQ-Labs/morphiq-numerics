"""Execute the predeclared matrix without building, profiling, or running oracles."""
from pathlib import Path
import csv,hashlib,json,math,os,statistics,subprocess,sys,time
P=Path(__file__).resolve().parent
manifest_path=P/'qualification-manifest.json';manifest=json.loads(manifest_path.read_text());cells=manifest['cells']
root=P/'qualification';root.mkdir(exist_ok=True)
frozen=hashlib.sha256(manifest_path.read_bytes()).hexdigest()
receipt=root/'manifest.sha256'
if receipt.exists():assert receipt.read_text().strip()==frozen
else:receipt.write_text(frozen+'\n')
for c in cells:
 assert hashlib.sha256(Path(c['product']).read_bytes()).hexdigest()==next(b['sha256'] for b in manifest['builds'] if b['name']==c['backend'])
 words=json.loads(Path(c['input']['file']).read_text());assert hashlib.sha256(b''.join(bytes.fromhex(w) for w in words)).hexdigest()==c['input']['sha256']

def command(c,out,proc):
 args=[sys.executable,str(P/'qualify-cell.py'),'--product',c['product'],'--primitive',c['primitive'],'--length',str(c['length']),'--population',c['input']['file'],'--kind',c['kind'],'--reference',c['reference'],'--counts',str(out/'counts.json'),'--target-ms','600','--cache-slots',str(c.get('cache_slots',1)),'--process',proc,'--out',str(out/proc)]
 if c['control']:args+=['--symbol-prefix','control_','--reference-product',str(P/'final-bin/control.so')]
 return args

def summaries():
 rows=[]
 for c in cells:
  out=root/c['id'];logs=[];ours=[];refs=[];durations=[]
  for i in range(10):
   f=out/str(i)/'samples.jsonl'
   if not f.exists() or not (out/(str(i)+'.complete')).exists():break
   samples=[json.loads(l) for l in f.read_text().splitlines() if json.loads(l)['kind']=='timed'];assert len(samples)==4
   pair=[]
   for r in range(2):
    a=next(x for x in samples if x['name']=='ours' and x['round']==r);b=next(x for x in samples if x['name']=='reference' and x['round']==r)
    pair.append(math.log(a['ns_per_call']/b['ns_per_call']));ours.append(a['ns_per_call']);refs.append(b['ns_per_call']);durations += [a['elapsed_ns'],b['elapsed_ns']]
   logs.append(statistics.median(pair))
  if len(logs)!=10:continue
  upper=math.exp(statistics.mean(logs)+manifest['protocol']['upper95_t9']*statistics.stdev(logs)/math.sqrt(10));ratio=math.exp(statistics.mean(logs));valid=min(durations)>=250_000_000
  row=dict(id=c['id'],required=c['required_parity'],ratio=ratio,upper95=upper,passes=valid and upper<=1,valid_duration=valid,minimum_sample_ns=min(durations),ours_median_ns=statistics.median(ours),reference_median_ns=statistics.median(refs),ours_min_ns=min(ours),ours_max_ns=max(ours),reference_min_ns=min(refs),reference_max_ns=max(refs),block_ratio_drift=math.exp(statistics.mean(logs[5:])-statistics.mean(logs[:5]))-1,process_log_ratios=logs)
  rows.append(row)
 (root/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
 if rows:
  with (root/'summary.csv').open('w') as stream:
   writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
 return rows

for block in range(2):
 for index,c in enumerate(cells):
  out=root/c['id'];out.mkdir(exist_ok=True)
  processes=(['calibration'] if block==0 else [])+[str(i) for i in range(block*5,(block+1)*5)]
  for proc in processes:
   done=out/(proc+'.complete')
   if done.exists():continue
   if (out/proc).exists():raise SystemExit(f'Incomplete/invalid attempt retained at {out/proc}; no automatic retry or count change')
   (root/'status.json').write_text(json.dumps(dict(block=block+1,cell=index+1,total=len(cells),id=c['id'],process=proc,utc=time.time()),indent=2)+'\n')
   with (out/(proc+'.log')).open('w') as stream:
    result=subprocess.run(command(c,out,proc),stdout=stream,stderr=subprocess.STDOUT)
   if result.returncode:raise SystemExit(f'Failed {c["id"]}/{proc}; evidence retained. See {out/(proc+".log")}')
   done.write_text(str(time.time())+'\n')
  if block==1:summaries()
  if (index+1)%10==0:print(f'Block {block+1}/2: {index+1}/{len(cells)} cells',flush=True)
rows=summaries();assert len(rows)==len(cells)
failures=[r for r in rows if r['required'] and not r['passes']]
result=dict(complete=True,cells=len(rows),required=sum(c['required_parity'] for c in cells),failures=[r['id'] for r in failures],all_required_pass=not failures)
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if failures:raise SystemExit('Required parity cells failed; do not claim qualification.')
