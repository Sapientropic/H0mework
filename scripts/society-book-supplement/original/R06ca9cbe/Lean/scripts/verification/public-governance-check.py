"""Independently replay the original journal and native owner/paid-response suffix."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import secrets
import sqlite3
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import public_key
from crypto import app_private,connect,digest,peer,receive,send,sign,verify
import governance
from recovery_loop import save
from source_semantics import Engine
from service import Store


def module(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
base=module('governance_inherited_ha','public-ha-check.py')
require=base.require;load=base.load;sha=base.sha


def physical_baseline():
    old=module('governance_paid_physical','public-distributed-audit.py')
    accepted=load(old.BOX/'acceptance.json');commit=load(old.BOX/'integration.json')['commit']
    # Historical placement signatures name their own installed release. Check
    # those exact Git bytes, while the current release is audited separately.
    with tempfile.TemporaryDirectory(prefix='public-original-protocol-') as temp:
        for name in ('anchor.py','crypto.py','quorum.py','challenge_anchor.py','remote_anchor.py'):
            path='Verification/public-audit/network/'+name
            raw=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
            require(hashlib.sha256(raw).hexdigest()==accepted['inputs'][path],'historical physical release changed')
            (Path(temp)/name).write_bytes(raw)
        old.NETWORK=Path(temp)
        original=Path(load(old.OLD/'acceptance.json')['actual'])
        old.independent(Path(accepted['actual']),original)
    final=load(old.BOX/'final-check.json')
    require(final['exit']==0 and sha(old.BOX/'acceptance.json')==final['acceptance_sha256'] and
            sha(old.BOX/'post-main-check.log')==final['independent_log_sha256'],'original physical acceptance provenance')


def runtime(box,manifest,current,*,feature='governance',expected_files=5210):
    installed=manifest[feature]['configurations'];out={}
    for member,cfg in installed.items():
        if member=='a':
            status=load(box/'runtime/ha-status.json')['body']['members']['a'];code_dir=str(NETWORK)
        else:
            status=current[member]['status']['body']['process'];code_dir=manifest['nodes'][member]['code']
        code=f'''import hashlib,json,os,shlex,subprocess,sys
from pathlib import Path
sys.path.insert(0,{code_dir!r})
from source_semantics import Engine
from recovery_loop import birth,boot_identity
cfg={cfg!r};owner={status!r};Engine(cfg)
assert owner['boot']==boot_identity() and birth(owner['pid'])==owner['birth']
workers=[]
for line in subprocess.check_output(['ps','-axo','pid=,ppid=,command='],text=True).splitlines():
 try:
  pid,parent,command=line.strip().split(None,2)
  if shlex.split(command)==cfg['backend'] and os.getpgid(int(parent))==owner['pgid']:
   workers.append({{'pid':int(pid),'parent':int(parent),'birth':birth(int(pid)),'boot':boot_identity()}})
 except (ValueError,ProcessLookupError):pass
assert len(workers)==1,workers
print(json.dumps({{'descriptor':cfg['descriptor'],'workers':workers,'verified_files':len(json.loads(Path(cfg['closure']).read_text()))}}))
'''
        if member=='a':value=json.loads(subprocess.check_output([sys.executable,'-c',code],text=True,cwd=ROOT))
        else:
            item=manifest['nodes'][member];value=json.loads(base.transport.remote(member,code,timeout=60,python=item['python']))
        require(value['descriptor']==manifest[feature]['descriptor'] and value['verified_files']==expected_files,'native '+feature+' view differs')
        out[member]=value
    print('LIVE NATIVE '+feature.upper()+' READERS PASS: '+''.join(sorted(installed))+'; exact '+str(expected_files)+' artifacts; compiler/exporter/argv; one owned worker per voting anchor',flush=True)
    return out


def new_window_refusal(box,cfg,local):
    state=load(box/'runtime/ha-status.json')['body'];owner=state['owner']
    # The current coordinator can change without changing the committed input.
    manifest=load(box/'ha/deployment.json');spark=manifest['nodes']['c']
    remote=json.loads(base.transport.remote('c',f"from pathlib import Path\nprint(Path({manifest['spark']['controller']['state']+'/ha-status.json'!r}).read_text())",python=spark['python']))['body']
    leader=state if state['phase']=='leader' else remote
    require(leader['phase']=='leader','no current service for typed continuation')
    host=load(box/'ha/addresses.json')['a' if leader['owner']=='mac' else 'c']
    profile=Path(cfg['pki'])/'auditor1'
    with connect(profile,cfg['port'],host=host,hostname='audit.local') as connection:
        key=peer(connection)[2];challenge=receive(connection);body=verify(key,'challenge',challenge)
        require((body['cut'],body['epoch'])==(22,6),'actual native next was not used for the challenge')
        message=sign(app_private(profile),'audit',{**body,'request_id':secrets.token_hex(16),'query':{'slots':63,'fields':3}})
        send(connection,message);reply=receive(connection)
        require(verify(key,'error',reply)=={'code':'NATIVE_NEW_SCOPE_REQUIRED'},'unsupported window was silently reused')
    require(base.database(Path(cfg['database']))==local,'typed new-window refusal changed payment or history')
    save(box/'ha/governance/new-window-refusal.json',{'challenge':challenge,'request':message,'response':reply})
    print('ACTUAL NEW-WINDOW REFUSAL PASS: native cut22/version6; no labor credit, deadline rewrite or extra event',flush=True)


def run(box,full,check_main):
    manifest=load(box/'ha/deployment.json');original=load(box/'service.json');cfg=manifest['mac']['service']
    local=base.database(Path(cfg['database']));literal=local['rows'];case=box/'ha/governance/actual-01'
    require(len(literal)==16 and literal[:14]==[tuple(r) for r in load(case/'before.json')['rows']],'original fourteen events changed')
    validator=object.__new__(Store);validator.config=cfg;validator.anchor=object()
    class PublicSigner:
        def public_key(self):return public_key(cfg['registry']['server'])
    validator.key=PublicSigner();validator.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:validator.validate_ledger();validator.validate_anchor_receipts()
    finally:validator.database.close()
    semantics={**manifest['semantic']['configurations']['a'],'error_log':str(box/'ha/governance/independent-source.log')}
    engine=Engine(semantics)
    try:engine.sync(literal)
    finally:engine.close()
    first=json.loads(literal[14][3])['body'];second=json.loads(literal[15][3])['body']
    birth=governance.expected(cfg,literal[:14],first);response=governance.expected(cfg,literal[:15],second)
    require(birth['labor']=='0' and birth['before']=={'holder':2,'version':5,'clock':'22'} and
            birth['next']=={'holder':2,'version':5,'clock':'23','cut':21} and len(birth['roles'])==1,'birth changed authority/material')
    require(response['labor']=='1' and response['next']=={'holder':None,'version':6,'clock':'24','cut':22} and
            response['rows'][1]=={'index':1,'signer':'1','kind':'revoke','accepted':True} and
            response['failures']==[{'index':2,'kind':'propose','expired':True,'gap':'1'}] and
            len(response['roles'])==1 and response['roles'][0]['principal']==birth['roles'][0]['principal'],'actual paid response differs')
    require(sum(int(json.loads(r[3])['body']['record']['labor']) for r in literal if json.loads(r[3])['body']['type']=='disclosure')==14,
            'original query payment changed')
    for tag,row in [('registration',literal[14]),('response',literal[15])]:
        result=load(case/(tag+'-result.json'))
        require(result['ledger']==json.loads(row[3]) and result['anchor']['body']['seq']==row[0],'actual delivery/lookup differs')
    print('INDEPENDENT ORIGINAL16 PASS: signed chain, requests, key rotation, unique operations, every QC; original labor14 plus native revoke1 once',flush=True)
    current=base.collect(box,manifest)
    n=base.transport.node('b')
    script="$v=(Get-CimInstance Win32_OperatingSystem).LastBootUpTime\n[DateTimeOffset]::new($v).ToUnixTimeSeconds()\n"
    result=n._run_remote([*n.ssh,'powershell','-NoProfile','-Command','-'],input=script.encode(),capture_output=True,timeout=30,allow_probe=False)
    require(result.returncode==0,'Windows boot read unavailable');current['b']['windows_boot_unix']=int(result.stdout.decode().strip())
    base.check_fault(box,manifest,original,literal);base.check_overlap(box,manifest)
    base.module('governance_alternating','public-ha-alternating-check.py').check(box,manifest,original,literal[:13])
    base.check_current(box,manifest,original,local,current)
    semantic=base.module('governance_semantic','public-semantic-check.py').check(box,manifest,original,literal,current)
    workers=runtime(box,manifest,current);new_window_refusal(box,cfg,local)
    if full:
        physical_baseline()
        result=subprocess.run([sys.executable,str(Path(__file__).with_name('public-source-final-audit.py')),'--check-main'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (box/'ha/governance/original-six-final.log').write_text(result.stdout)
        require(result.returncode==0,'original six/full-cost independent audit failed: '+result.stdout[-1800:])
        print('ORIGINAL SIX/FULL COST PASS: fresh independent source audit and historical physical raw-evidence replay',flush=True)
    files=['Verification/public-audit/network/'+name for name in manifest['protocol']]
    files+=['Verification/public-audit/network/client.py']
    files+=['Lean/scripts/verification/'+name for name in ['public-governance-source.lean','public-governance-deploy.py','public-governance-local.py','public-governance-actual.py','public-governance-check.py','public-network-frame-check.py','public-ha-deploy.py','public-ha-check.py','public-semantic-check.py']]
    files+=['Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/'+name for name in ['Response.lean','Response/Runtime.lean','Governance.lean','Governance/Runtime.lean']]
    inputs={name:sha(ROOT/name) for name in files}
    if check_main:
        for name,wanted in inputs.items():require(hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+name],cwd=ROOT)).hexdigest()==wanted,'main differs: '+name)
        print('NATIVE GOVERNANCE MAIN INTEGRATION PASS',flush=True)
    save(box/'ha/governance/final-check.json',{'exit':0,'events':16,'original_labor':14,'response_labor':1,'head':literal[-1][2],
      'inputs':inputs,'workers':workers,'semantic':semantic,'full':full,'main_verified':check_main,'windows_boot_unix':current['b']['windows_boot_unix'],
      'source_gap':{'kind':'NATIVE_NEW_SCOPE_REQUIRED','cut':22,'labor_gap':'1','expired':True},'at':time.time()})
    print('INDEPENDENT NATIVE GOVERNANCE AUDIT ACCEPTED',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    try:run(a.box.resolve(),a.full,a.check_main)
    finally:governance.close_readers()
