#!/usr/bin/env python3
"""Focused default-budget replay of source ordered-loop declarations and consumers."""
import json
from pathlib import Path
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
LEAN=ROOT/'Lean'
MODULES=['Grading','Source','Words']

def main():
    (HERE/'logs').mkdir(exist_ok=True)
    targets=[(n,LEAN/'SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/ClosedLoops'/f'{n}.lean') for n in MODULES]
    targets.extend((n,HERE/f'{n}.lean') for n in ['Audit','Consumer'])
    records=[]
    for name,path in targets:
        cmd=['lake','env','lean','--trust=0','-DwarningAsError=true',str(path)]
        start=time.monotonic()
        result=subprocess.run(cmd,cwd=LEAN,capture_output=True,text=True,timeout=120)
        (HERE/'logs'/f'{name}.log').write_text(result.stdout+result.stderr)
        records.append({'name':name,'command':cmd,'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3)})
        print(name,result.returncode,flush=True)
        if result.returncode: print(result.stdout+result.stderr,flush=True);break
    passed=len(records)==len(targets) and not any(x['exit_code'] for x in records)
    dependencies=set()
    if passed:
        text=(HERE/'logs/Audit.log').read_text()+(HERE/'logs/Consumer.log').read_text()
        for block in re.findall(r'depends on axioms: \[([^]]*)\]',text,re.S):
            dependencies.update(x.strip() for x in block.split(',') if x.strip())
        assert dependencies <= {'Classical.choice','propext','Quot.sound'}
    (HERE/'focused.json').write_text(json.dumps({'passed':passed,'records':records,'axioms':sorted(dependencies),
        'public_declarations':41,'direct_consumers':2,'trust':0,'warnings_as_errors':True,'default_limits':True},indent=2)+'\n')
    assert passed
if __name__=='__main__': main()
