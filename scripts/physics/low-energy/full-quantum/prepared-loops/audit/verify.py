#!/usr/bin/env python3
"""Independent strict check of the actual preparation-weighted complete words."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import re
import subprocess
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
LEAN=ROOT/'Lean'
FILES=['Source','Words','Native','Transfer','Scalar']


def check(row):
    name,path=row;command=['lake','env','lean','--trust=0','-DwarningAsError=true',str(path)]
    started=time.monotonic();result=subprocess.run(command,cwd=LEAN,capture_output=True,text=True)
    (HERE/f'{name}-strict.log').write_text(result.stdout+result.stderr)
    print(name,result.returncode,flush=True)
    return {'name':name,'command':command,'exit_code':result.returncode,'seconds':round(time.monotonic()-started,3)}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--consumer-only',action='store_true')
    args=parser.parse_args()
    targets=[(name,LEAN/'SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/PreparedLoops'/f'{name}.lean') for name in FILES]
    targets += [(name,HERE.parent/f'{name}.lean') for name in ['Audit','Consumer']]
    targets += [('IndependentConsumer',HERE/'Consumer.lean')]
    if args.consumer_only:
        records=[check(targets[-1])]
        old=json.loads((HERE/'focused.json').read_text())
        old['checks']=[records[0] if row['name']=='IndependentConsumer' else row for row in old['checks']]
        (HERE/'focused.json').write_text(json.dumps(old,indent=2)+'\n')
    else:
        with ThreadPoolExecutor(max_workers=3) as pool:records=list(pool.map(check,targets))
        for name,path in targets[:len(FILES)]:
            lint=subprocess.run(['python3',str(ROOT/'.agents/skills/lean-agent/scripts/theorem_mouth_lint.py'),str(path),'--fail-on','never'],cwd=ROOT,capture_output=True,text=True)
            (HERE/f'{name}-mouth.log').write_text(lint.stdout+lint.stderr)
        (HERE/'focused.json').write_text(json.dumps({'checks':records,'trust':0,'warnings_as_errors':True,'default_limits':True},indent=2)+'\n')
    assert all(row['exit_code']==0 for row in records)
    statements={}
    for name in ['Audit','Consumer','IndependentConsumer']:
        log=(HERE/f'{name}-strict.log').read_text()
        for declaration,block in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S):
            statements[declaration]=sorted(v.strip() for v in block.split(',') if v.strip())
        for declaration in re.findall(r"'([^']+)' does not depend on any axioms",log):statements[declaration]=[]
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in statements.values())
    (HERE/'trust-summary.json').write_text(json.dumps({'count':len(statements),'declarations':statements},indent=2)+'\n')


if __name__=='__main__':main()
