"""Independent consumption of the original journal's productive source successor."""
import argparse
from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import re

ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import public_key
from crypto import canonical,digest
from recovery_loop import save
from service import Store
import productive_extension,productive_regeneration
from cryptography.exceptions import InvalidSignature


def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


deploy=module('productive_live_deploy','public-productive-deploy.py')
prior=module('productive_prior_check','public-material-check.py')
native=module('productive_material_replay','public-productive-check.py')
load,sha=deploy.load,deploy.sha


def closed_replay(box):
    home=deploy.location(box);directory=home/'actual';manifest=prior.old.old.live.public_closed(box,directory)
    cfg=manifest['mac']['service'];rows=load(directory/'events.json');argument,_,_=productive_regeneration.context(cfg,rows)
    assert argument==load(directory/'source-input.json')
    expected=[json.loads(r[3])['body']['native'] for r in rows if json.loads(r[3])['body']['type']==productive_regeneration.KIND]
    parent=[json.loads(r[3])['body']['native'] for r in rows[:53] if json.loads(r[3])['body']['type'] in {'energy-regeneration','energy-material'}]
    script=ROOT/'Lean/scripts/verification/public-productive-owner-source.lean';env=os.environ.copy();env['LEAN_PATH']=cfg['productive']['lean_path'];answers={}
    for branch in ('private-one','private-two'):
        command=[cfg['productive']['backend'][0],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',str(script),branch]
        result=subprocess.run(command,cwd=ROOT/'Lean',env=env,input=canonical(argument)+b'\n',stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=600)
        (directory/(branch+'.json')).write_bytes(result.stdout);(directory/(branch+'.stderr')).write_bytes(result.stderr)
        assert result.returncode==0 and not result.stderr,(result.returncode,result.stderr[-1500:])
        answer=json.loads(result.stdout);assert answer['prior']==parent and answer['output']==expected
        assert answer['history']==31 and answer['nativeSlots']==18 and answer['nativeOutstanding']=='0'
        assert len(answer['initialOrigins'])==12 and len(answer['origins'])==18
        assert answer['origins'][:12]==answer['initialOrigins']
        assert answer['ownFrame']==('39' if branch=='private-one' else '38');answers[branch]=answer
    assert answers['private-one']['output']==answers['private-two']['output']
    assert answers['private-one']['origins']==answers['private-two']['origins']
    save(directory/'owner-accepted.json',dict(events=sha(directory/'events.json'),closed=sha(directory/'closed.json'),input=digest(argument),source=sha(script),
        branches={k:sha(directory/(k+'.json')) for k in answers},replies=68,frames=['39','38'],native_slots=18,native_outstanding='0'))
    print('INDEPENDENT CLOSED PRODUCTIVE PASS: 68 exact replies; own frames39/38; 18 original native origins; zero outstanding',flush=True)


def run(box,full=False,check_main=False):
    home=deploy.location(box);directory=home/'actual';manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service']
    rows=[list(r) for r in deploy.roll.spare.rows(cfg['database'])];before=load(directory/'before.json')
    assert before==load(home.parent/'refeed/actual/events.json') and rows[:53]==before and len(rows)==68
    activated,certificate=productive_extension.require(cfg,rows)
    assert activated==54 and certificate==load(home/'admission.json')
    previous=load(home/'online-before.json');assert cfg['material_extension']==previous['mac']['service']['material_extension']
    assert manifest['native_admission']==previous['native_admission']
    historical=load(home.parent/'refeed/final-check.json');assert historical['exit']==0 and historical['events']==53 and historical['head']==before[-1][2]
    commit=load(home.parent/'refeed/integration.json')['commit']
    subprocess.run(['git','merge-base','--is-ancestor',commit,'refs/heads/main'],cwd=ROOT,check=True)
    for path,wanted in historical['inputs'].items():assert prior.old.sha_bytes(subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT))==wanted
    checker=object.__new__(Store);checker.config=cfg;checker.anchor=object()
    class Signer:
        def public_key(self):return public_key(cfg['registry']['server'])
    checker.key=Signer();checker.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    print('INDEPENDENT PRODUCTIVE AUDIT: original68 signed ledger and source replay',flush=True)
    try:checker.validate_ledger();checker.validate_anchor_receipts()
    finally:checker.database.close();prior.old.old.release_readers()
    events=[json.loads(r[3])['body'] for r in rows[activated:]]
    commands=[e['request']['body']['command'] for e in events]
    generated,scope,current=productive_regeneration.context(cfg,rows)
    assert generated==load(directory/'source-input.json')
    outputs=[e['native'] for e in events];parent=json.loads(before[-1][3])['body']['native']
    witness=dict(parent=[parent],initial=parent['next'],output=outputs,public=outputs,next=outputs[13]['next'])
    material=native.verify(witness,commands,parent,require_finance=False)
    dual=0
    for output in outputs:
        for packet in output.get('packets',[]):
            assert [e['slot'] for e in packet]==list(range(6))
            for evidence in packet:
                assert prior.old.privacy.original._dual.payment_scan(evidence['slot'],evidence)=='verified'
                assert prior.old.privacy.original._dual.lifecycle_replay(evidence['slot'],evidence)=='verified'
                dual+=2
    assert dual==24
    material['dual_checks']=dual
    assert load(home/'continuity-output.json')['public']==outputs,'ACTUAL_ADMITTED_SOURCE_LITERAL'
    negative=[]
    for name in ('free-factory','invented-waste','erase-live-debt','repaid-bootstrap'):
        changed=deepcopy(witness)
        if name=='free-factory':changed['output'][1]['rows'][0]['debit']=[]
        elif name=='invented-waste':changed['output'][1]['rows'][0]['credit'][1][2]='2'
        elif name=='erase-live-debt':next(v for v in changed['output'][0]['next']['claims'] if v[:3]==['delivery','provider:0','audit:3'])[3]='0'
        else:changed['output'][1]['rows']=changed['output'][0]['rows'][4:5]+changed['output'][1]['rows']
        changed['public']=deepcopy(changed['output'])
        try:native.verify(changed,commands,parent,require_finance=False)
        except (AssertionError,KeyError):negative.append(name)
        else:raise AssertionError('PRODUCTIVE_MUTATION_ACCEPTED:'+name)
    for name,change in [('parent',lambda c:c['point'].update(parent='0'*64)),('missing-vote',lambda c:c['votes'].pop()),('descriptor',lambda c:c['point']['descriptor'].update(exporter_sha256='0'*64))]:
        changed=deepcopy(certificate);change(changed)
        try:productive_extension.admission(cfg,changed)
        except (ValueError,InvalidSignature):negative.append(name)
        else:raise AssertionError('PRODUCTIVE_ADMISSION_MUTATION_ACCEPTED:'+name)
    transport=prior.wire(box,manifest,home,rows,before,expected_events=15)
    owner=load(directory/'owner-accepted.json')
    assert owner['events']==sha(directory/'events.json') and owner['closed']==sha(directory/'closed.json')
    assert owner['source']==sha(ROOT/'Lean/scripts/verification/public-productive-owner-source.lean')
    for branch,wanted in owner['branches'].items():assert sha(directory/(branch+'.json'))==wanted
    counts=prior.old.replicas(box,manifest,rows,home,'productive')
    module('productive_runtime_observer','public-productive-actual.py').wait_runtime(box,manifest)
    prior.old.current_runtime(box,manifest,rows,home)
    application=module('productive_historical_application','public-application-check.py').check(box,check_main)
    if full:
        audit=subprocess.run([sys.executable,str(ROOT/'.agents/tmp/public-autonomous-origin-20261101/final-audit/verify.py')],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (home/'full-cost.log').write_text(audit.stdout);assert audit.returncode==0,audit.stdout[-1600:];print(audit.stdout,end='',flush=True)
    kernel=load(home/'kernel.json');axioms=load(home/'axioms.json')
    assert kernel['exit']==0 and axioms['exit']==0 and axioms['mouths']==16
    assert set(axioms['axioms'])=={'propext','Classical.choice','Quot.sound'}
    assert axioms['sources']==kernel['sources'] and sha(home/axioms['log'])==axioms['log_sha256']
    mouths=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(home/axioms['log']).read_text(),re.S)
    assert len(mouths)==16 and all(set(a.replace('\n','').replace(' ','').split(','))==set(axioms['axioms']) for _,a in mouths)
    inputs={}
    for name,wanted in kernel['sources'].items():
        path='Lean/'+name.replace('.','/')+'.lean';assert sha(ROOT/path)==wanted;inputs[path]=wanted
    files=[Path(__file__),*[Path(__file__).with_name('public-productive-'+n) for n in ('deploy.py','actual.py','check.py','source.lean','network-source.lean','owner-source.lean')],
        *[Path(__file__).with_name(n) for n in ('public-ha-check.py','public-material-check.py','public-supply-check.py','public-supply-actual.py')],*[NETWORK/n for n in manifest['protocol']]]
    inputs.update({str(p.relative_to(ROOT)):sha(p) for p in files})
    if check_main:
        for path,wanted in inputs.items():assert prior.old.sha_bytes(subprocess.check_output(['git','show','refs/heads/main:'+path],cwd=ROOT))==wanted,('MAIN_SOURCE_CHANGED',path)
    report=dict(exit=0,events=68,head=rows[-1][2],original_events=53,productive=material,wire=transport,replicas=counts,
                kernel=kernel,axioms=axioms,application_receipts=application,negative_controls=negative,inputs=inputs,current=current,scope=scope,full=full,main_verified=check_main)
    save(home/'final-check.json',report)
    print('INDEPENDENT PRODUCTIVE LIVE AUDIT PASS '+json.dumps({k:report[k] for k in ('events','productive','wire','replicas','current','main_verified')},sort_keys=True),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');p.add_argument('--closed',action='store_true');a=p.parse_args()
    if a.closed:closed_replay(a.box.resolve())
    else:run(a.box.resolve(),a.full,a.check_main)
