"""Independent original24, recursive actual supply and paid successor audit."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from recovery_loop import save
from service import Store
from source_semantics import Engine
import continuation
import energy
import governance
spec=importlib.util.spec_from_file_location('continuation_energy_check',Path(__file__).with_name('public-energy-check.py'))
previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
old=previous.old;base=previous.base;require=base.require;load=base.load;sha=base.sha


def run(box,full,check_main):
    manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service'];original=load(box/'service.json')
    current_rows=base.database(Path(cfg['database']));literal=current_rows['rows']
    case=box/'ha/continuation/actual-01'
    require(len(literal)==24 and literal[:18]==[tuple(row) for row in load(case/'before.json')['rows']],
            'original18 or expected actual24 differs')
    require(literal[:18]==[tuple(row) for row in load(box/'ha/energy/actual-01/after.json')['rows']],
            'immutable original energy source prefix differs')
    validator=object.__new__(Store);validator.config=cfg;validator.anchor=object()
    class PublicSigner:
        def public_key(self):return public_key(cfg['registry']['server'])
    validator.key=PublicSigner();validator.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:validator.validate_ledger();validator.validate_anchor_receipts()
    finally:validator.database.close()
    engine=Engine({**manifest['semantic']['configurations']['a'],'replay_seconds':180,
                   'error_log':str(box/'ha/continuation/independent-source.log')})
    try:engine.sync(literal)
    finally:engine.close()
    for number in (16,17):
        energy.expected(cfg,literal[:number],json.loads(literal[number][3])['body'])
    tests=[]
    for number in range(18,24):
        event=json.loads(literal[number][3])['body']
        checked=continuation.expected(cfg,literal[:number],event)
        tests.append((event,checked))
    repair,revoke,early,deadline,reopen,grant=[event['native'] for event,_ in tests]
    require([r['accepted'] for r in repair['rows']]==[False,True,True,True] and
            repair['next']['energy']==['6','2','0','3'] and
            tests[0][1]==[dict(payment=['verified'],lifecycle=['verified'])], 'refusal/supply/retry differs')
    require([r['accepted'] for r in revoke['rows']]==[True,False] and revoke['next']['holder'] is None
            and revoke['next']['version']==9 and revoke['next']['energy']==['5','2','0','3']
            and not revoke['packets'], 'paid revoke or rejected old authority differs')
    require(all(n['reason']=='WINDOW_ACTIVE' and not n['rows'] and not n['packets'] for n in (early,deadline)),
            'premature opening charged or disclosed')
    require(reopen['reason']=='OPENED' and reopen['scope']['deadline']=='32' and
            reopen['next']['energy']==['4','2','0','3'] and reopen['nextScope']==grant['scope']
            and (grant['scope']['earliest'],grant['scope']['deadline'])==('35','41'), 'actual next window differs')
    require(grant['next']['energy']==['2','0','0','3'] and grant['next']['holder']==1 and
            grant['next']['version']==11 and tests[-1][1]==[dict(payment=['verified'],lifecycle=['verified'])],
            'new paid authority/delivery differs')
    require(all(n['next']['labor']==['0']*4 for n in (repair,revoke,early,deadline,reopen,grant)), 'old labor credited')
    tags=load(box/'ha/continuation/actual.json')['tags']
    for number,tag in enumerate(tags,18):
        result=load(case/(tag+'-result.json'));lookup=load(case/(tag+'-lookup.json'))
        require(result['ledger']==json.loads(literal[number][3]) and lookup['body']['result']['ledger']==result['ledger'],
                'original request lookup changed payment: '+tag)
    controls=load(box.parent/'mandate/continuation-controls-02/accepted.json')
    require(len(controls['tests'])==18 and controls['inputs']=={name:sha(ROOT/name) for name in controls['inputs']},'recursive controls absent or source changed')
    print('INDEPENDENT ORIGINAL24 PASS: original18 unchanged; refusal+transfer3+retry; paid revoke; two unpaid blocks; new window35-41; fresh paid grant/delivery; six exact original lookups',flush=True)
    current=base.collect(box,manifest)
    node=base.transport.node('b')
    script="$v=(Get-CimInstance Win32_OperatingSystem).LastBootUpTime\n[DateTimeOffset]::new($v).ToUnixTimeSeconds()\n"
    result=node._run_remote([*node.ssh,'powershell','-NoProfile','-Command','-'],input=script.encode(),capture_output=True,timeout=30,allow_probe=False)
    require(result.returncode==0,'Windows boot read unavailable');current['b']['windows_boot_unix']=int(result.stdout.decode().strip())
    base.check_fault(box,manifest,original,literal);base.check_overlap(box,manifest)
    base.module('continuation_alternating','public-ha-alternating-check.py').check(box,manifest,original,literal[:13])
    base.check_current(box,manifest,original,current_rows,current)
    semantic=base.module('continuation_semantic','public-semantic-check.py').check(box,manifest,original,literal,current)
    old.runtime(box,manifest,current)
    previous.native_workers(box,manifest,current)
    workers=old.runtime(box,manifest,current,feature='continuation',expected_files=5214)
    native_config=manifest['continuation']['configurations']['a']
    with tempfile.TemporaryDirectory(prefix='public-continuation-kernel-') as temp:
        for name,wanted in manifest['continuation']['descriptor']['modules'].items():
            output=Path(temp)/Path(name).name;source=name.removesuffix('.olean')+'.lean'
            result=subprocess.run([native_config['backend'][0],'--trust=0','-DwarningAsError=true','-o',str(output),source],cwd=ROOT/'Lean',env={**os.environ,'LEAN_PATH':native_config['lean_path']},text=True,capture_output=True)
            require(result.returncode==0 and sha(output)==wanted,'strict installed source rebuild differs: '+source+' '+result.stdout[-1000:])
    mouths=['first_is_actual_generated_next','Window.current_is_own_root_current','Window.emission_uses_exact_request',
      'Window.preserves_every_claim','Window.renewal_has_exact_next','Window.opening_is_actual_paid_application',
      'Window.failed_open_has_typed_reason','Window.every_material_flow','access_valid_iff',
      'Delivery.authority_is_paid_and_within_the_new_window','Delivery.service_really_debits_the_candidate',
      'Delivery.delivery_really_debits_the_service','Delivery.both_independent_checks_consume_the_original_service',
      'Runtime.shares_actual_writeback_and_generated_next','Runtime.successor_is_installed_output']
    namespace='SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Continuation'
    with tempfile.TemporaryDirectory(prefix='public-continuation-axioms-') as temp:
        path=Path(temp)/'Axioms.lean';path.write_text('import '+namespace+'.Runtime\n'+''.join('#print axioms '+namespace+'.'+name+'\n' for name in mouths))
        result=subprocess.run([native_config['backend'][0],'--trust=0',str(path)],cwd=ROOT/'Lean',env={**os.environ,'LEAN_PATH':native_config['lean_path']},text=True,capture_output=True)
        require(result.returncode==0 and result.stdout.count('depends on axioms:')==len(mouths),'axiom replay failed: '+result.stdout[-1000:])
        for block in re.findall(r'depends on axioms: \[(.*?)\]',result.stdout,re.S):
            require(set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',block))<={'propext','Classical.choice','Quot.sound'},'nonstandard axiom')
        (box/'ha/continuation/axioms.log').write_text(result.stdout)
    print('CONTINUATION KERNEL/INSTALLATION PASS: two exact trust0/warningAsError rebuilds; 15 standard-axiom mouths; three independent 5214-artifact live readers',flush=True)
    if full:
        old.physical_baseline()
        result=subprocess.run([sys.executable,str(Path(__file__).with_name('public-source-final-audit.py')),'--check-main'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (box/'ha/continuation/original-six-final.log').write_text(result.stdout)
        require(result.returncode==0,'original six/full cost audit failed: '+result.stdout[-1800:])
        print('ORIGINAL SIX/FULL COST PASS: fresh final audit and original 514-event physical replay',flush=True)
    files=['Verification/public-audit/network/'+name for name in manifest['protocol']]
    files+=['Verification/public-audit/network/client.py']
    files+=['Lean/scripts/verification/public-continuation-'+name for name in ['source.lean','deploy.py','actual.py','local.py','check.py']]
    files+=['Lean/scripts/verification/public-ha-check.py']
    files+=['Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/'+name for name in ['Continuation.lean','Continuation/Runtime.lean']]
    inputs={name:sha(ROOT/name) for name in files}
    if check_main:
        for name,wanted in inputs.items():require(hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+name],cwd=ROOT)).hexdigest()==wanted,'main differs: '+name)
        print('RECURSIVE SUPPLY MAIN INTEGRATION PASS',flush=True)
    save(box/'ha/continuation/final-check.json',{'exit':0,'events':24,'head':literal[-1][2],
      'supplier_transfer':3,'energy_consumed':8,'new_window':[35,41],'old_window':[26,32],
      'inputs':inputs,'workers':workers,'semantic':semantic,'axiom_mouths':15,'kernel_modules':2,
      'full':full,'main_verified':check_main,'at':time.time()})
    print('INDEPENDENT RECURSIVE SUPPLY AUDIT ACCEPTED',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    try:run(a.box.resolve(),a.full,a.check_main)
    finally:governance.close_readers();energy.close_readers()
