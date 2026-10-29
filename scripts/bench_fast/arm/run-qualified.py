import csv,datetime,json,os,pathlib,subprocess,sys,time
P=pathlib.Path(__file__).resolve().parent
cells=json.loads((P/'cells.json').read_text());groups=json.loads((P/'groups.json').read_text())
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def host(label):
 records=[]
 for cmd in [['pmset','-g','batt'],['pmset','-g','therm'],['sysctl','vm.loadavg'],['ps','-eo','pid,pcpu,comm']]:
  r=subprocess.run(cmd,text=True,capture_output=True);records.append(dict(command=cmd,code=r.returncode,stdout=r.stdout,stderr=r.stderr))
 (P/'host'/f'{label}.json').write_text(json.dumps(dict(utc=stamp(),records=records),indent=2)+'\n')
def cell_run(c,phase):
 with (P/'logs'/f'cell-{c}-{phase}.log').open('x') as f:subprocess.run([sys.executable,str(P/'qualify-cell.py'),c,str(phase)],cwd=P,stdout=f,stderr=subprocess.STDOUT,check=True)
(P/'logs').mkdir();(P/'host').mkdir();host('before')
for group,ids in groups.items():
 print(stamp(),group,'calibration',len(ids),'cells',flush=True)
 for c in ids:cell_run(c,'calibration')
 for process in range(10):
  if process==5:host(group+'-block1-end');time.sleep(30)
  print(stamp(),group,'process',process,flush=True)
  order=ids if process%2==0 else ids[::-1]
  for i,c in enumerate(order):
   cell_run(c,process)
   if i%10==9:host(f'{group}-{process}-{i}')
  host(f'{group}-{process}-end')
  for c in ids:
   with (P/'qualified'/c/str(process)/'samples.csv').open() as samples:
    if any(r['kind']=='timed' and int(r['elapsed_ns'])<250000000 for r in csv.DictReader(samples)):
     raise SystemExit('Duration prerequisite failed: retain all observations; stop before further processes')
 subprocess.run([sys.executable,str(P/'summarize.py')],check=True)
 summary=json.loads((P/'qualification-summary.json').read_text())
 if summary['required_failed'] or summary['duration_failed']:
  raise SystemExit('Campaign paused after completed group: retain failed cells; investigate before further timing')
host('after');(P/'COMPLETE').write_text(stamp()+'\n')
