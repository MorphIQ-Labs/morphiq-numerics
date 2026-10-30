#!/usr/bin/env python3
"""One-process exploratory screen of the declared cells, never qualification.

Retains every calibration and sample. An interrupted cell is not retried.
Use the ten-process runner for any parity claim.
"""
import argparse
import json
import math
from pathlib import Path
import subprocess
import sys

P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--limit',type=int)
a=ap.parse_args()
cells=json.loads((P/'qualification-manifest.json').read_text())['cells']
root=P/'screen';root.mkdir(exist_ok=True)
rows=[]
for c in cells[:a.limit]:
    out=root/c['id'];out.mkdir(exist_ok=True)
    command=[sys.executable,str(P/'qualify-cell.py'),'--product',c['product'],
             '--primitive',c['primitive'],'--length',str(c['length']),
             '--population',c['input']['file'],'--kind',c['kind'],
             '--reference',c['reference'],'--counts',str(out/'counts.json'),
             '--target-ms','150','--cache-slots',str(c['cache_slots']),'--diagnostic']
    if c['control']:command+=['--symbol-prefix','control_','--reference-product',c['control_product']]
    for proc in ['calibration','0']:
        done=out/(proc+'.complete')
        if done.exists():continue
        if (out/proc).exists():raise SystemExit('Interrupted attempt retained: '+str(out/proc))
        with (out/(proc+'.log')).open('w') as log:
            subprocess.run(command+['--process',proc,'--out',str(out/proc)],stdout=log,stderr=subprocess.STDOUT,check=True)
        done.touch()
    samples=[json.loads(l) for l in (out/'0/samples.jsonl').read_text().splitlines() if json.loads(l)['kind']=='timed']
    ratios=[next(s['ns_per_call'] for s in samples if s['name']=='ours' and s['round']==i)/next(s['ns_per_call'] for s in samples if s['name']=='reference' and s['round']==i) for i in range(2)]
    row=dict(id=c['id'],required=c['required_parity'],paired_ratios=ratios,ratio=math.sqrt(ratios[0]*ratios[1]))
    rows.append(row)
    (root/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(c['id'],round(row['ratio'],4),flush=True)
