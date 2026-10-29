import csv,datetime,json,math,os,sys
import matrix as M
P=M.P;cell=M.CELLS[int(sys.argv[1])];phase=sys.argv[2];base=P/'qualified'/cell['id'];out=base/phase;out.mkdir(parents=True)
meta=dict(cell=cell,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pid=os.getpid(),load_before=os.getloadavg(),qos='QOS_CLASS_USER_INITIATED',qos_result=M.E.QOS_RESULT,affinity='macOS unbound')
if phase=='calibration':
 from protocol import calibrate
 counts={};rows=[]
 for name in cell['pair']:
  def record(kind,count,elapsed):
   rows.append(dict(name=name,kind=kind,iterations=count,elapsed_ns=elapsed))
   (out/'samples.json').write_text(json.dumps(rows,indent=2)+'\n')
  counts[name]=calibrate(lambda count:M.measure(cell,name,count),record)
 (base/'counts.json').write_text(json.dumps(counts,indent=2)+'\n')
else:
 process=int(phase);counts=json.loads((base/'counts.json').read_text())
 with (out/'samples.csv').open('w',buffering=1) as f:
  w=csv.DictWriter(f,fieldnames=['cell','process','round','name','kind','iterations','elapsed_ns','ns_per_call']);w.writeheader()
  for rep in range(2):
   pair=cell['pair'] if (process+rep)%2==0 else cell['pair'][::-1]
   for name in pair:
    for kind,count in [('warmup',max(1,counts[name]//2)),('timed',counts[name])]:
     elapsed=M.measure(cell,name,count);w.writerow(dict(cell=cell['id'],process=process,round=rep,name=name,kind=kind,iterations=count,elapsed_ns=elapsed,ns_per_call=elapsed/count))
meta['load_after']=os.getloadavg();meta['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
