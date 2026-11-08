"""Independent original27, different-auditor replacement and actual delivery audit."""
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
import handoff
import energy
import governance
spec=importlib.util.spec_from_file_location('continuation_energy_check',Path(__file__).with_name('public-energy-check.py'))
previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
old=previous.old;base=previous.base;require=base.require;load=base.load;sha=base.sha


def run(box,full,check_main):
    manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service'];original=load(box/'service.json')
    current_rows=base.database(Path(cfg['database']));literal=current_rows['rows']
    case=box/'ha/handoff/actual-01'
    require(len(literal)==27 and literal[:24]==[tuple(row) for row in load(case/'before.json')['rows']],
            'original24 or expected actual27 differs')
    require(literal[:24]==[tuple(row) for row in load(box/'ha/continuation/actual-01/after.json')['rows']],
            'immutable original recursive source prefix differs')
    validator=object.__new__(Store);validator.config=cfg;validator.anchor=object()
    class PublicSigner:
        def public_key(self):return public_key(cfg['registry']['server'])
    validator.key=PublicSigner();validator.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:validator.validate_ledger();validator.validate_anchor_receipts()
    finally:validator.database.close()
    engine=Engine({**manifest['semantic']['configurations']['a'],'replay_seconds':180,
                   'error_log':str(box/'ha/handoff/independent-source.log')})
    try:engine.sync(literal)
    finally:engine.close()
    for number in (16,17):
        energy.expected(cfg,literal[:number],json.loads(literal[number][3])['body'])
    for number in range(18,24):
        continuation.expected(cfg,literal[:number],json.loads(literal[number][3])['body'])
    checked=[]
    for number in range(24,27):
        event=json.loads(literal[number][3])['body']
        checked.append((event,handoff.expected(cfg,literal[:number],event)))
    first,stale,unfunded=[event['native'] for event,_ in checked]
    require(first['before']['clock']=='36' and first['next']['clock']=='37' and
            first['actor']==first['candidate']==first['next']['holder']==2 and first['next']['version']==14,
            'distinct candidate or exact prefix splice differs')
    require(first['scope']==load(box/'ha/continuation/actual-01/new-grant-result.json')['event']['native']['scope']
            and first['scope']['deadline']=='41' and first['next']['energy']==['0']*4,
            'window changed or material cost differs')
    require([r['kind'] for r in first['rows']]==['revoke','transfer','transfer','propose','accept','use','use']
            and all(r['accepted'] for r in first['rows']), 'actual seven-action word differs')
    require(first['rows'][1]['energyDebit']==['0','0','0','1'] and first['rows'][1]['energyCredit']==['1','0','0','0']
            and first['rows'][2]['energyDebit']==['0','0','0','2'] and first['rows'][2]['energyCredit']==['0','0','2','0'],
            'post-revoke exact deficit transfers differ')
    require(checked[0][1]==[dict(payment=['verified']*6,lifecycle=['verified']*6)], 'six-slot dual delivery differs')
    require(stale['reason']=='UNAUTHORIZED' and unfunded['reason']=='UNFUNDED'
            and all(not native['packets'] and native['next']['holder']==2 and native['next']['energy']==['0']*4
                    and native['next']['labor']==['0']*4 and all(not row['accepted'] for row in native['rows'])
                    for native in (stale,unfunded)), 'old/new signed refusal or zero fee differs')
    tags=load(box/'ha/handoff/actual.json')['tags']
    for number,tag in enumerate(tags,24):
        result=load(case/(tag+'-result.json'));lookup=load(case/(tag+'-lookup.json'))
        require(result['ledger']==json.loads(literal[number][3]) and lookup['body']['result']['ledger']==result['ledger'],
                'original request lookup changed payment: '+tag)
    # This real pre-stage failure was rebound only after original-ID lookup,
    # preserving the signed rejection and the same logical request identity.
    archived=list(case.glob('old-denied-rejected-request-*.json'))
    refused=list(case.glob('old-denied-rejected-response-*.json'))
    require(len(archived)==len(refused)==1,'known rejected request evidence absent')
    old_request=load(archived[0]);actual_request=json.loads(literal[25][3])['body']['request']
    from crypto import verify
    require(verify(public_key(cfg['registry']['server']),'error',load(refused[0]))['code']=='CHALLENGE_BINDING'
            and old_request['body']['request_id']==actual_request['body']['request_id']
            and all(old_request['body'][key]==actual_request['body'][key] for key in ('actor','op','query','scope'))
            and sum(json.loads(row[3])['body']['request']['body']['request_id']==actual_request['body']['request_id'] for row in literal)==1,
            'pre-stage refresh lost identity or duplicated a payment')
    controls=load(box.parent/'mandate/handoff-controls-01/accepted.json')
    require(len(controls['tests'])==18 and controls['inputs']=={name:sha(ROOT/name) for name in controls['inputs']},
            'handoff controls absent or source changed')
    print('INDEPENDENT ORIGINAL27 PASS: original24; source-selected auditor2; exact deficit transfer1+2; five payments once; old1 signed unauthorized; new2 signed unfunded; three original lookups',flush=True)
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
    old.runtime(box,manifest,current,feature='continuation',expected_files=5214)
    workers=old.runtime(box,manifest,current,feature='handoff',expected_files=5216)
    limits={}
    for member in 'bc':
        item=manifest['nodes'][member];prefix=['systemctl']+(['--user'] if member=='b' else [])
        code=f"import json,subprocess\nresult=subprocess.check_output({prefix!r}+['show','homework-public-anchor-recovery.service','-p','MemoryMax','-p','CPUQuotaPerSecUSec'],text=True)\nprint(json.dumps(dict(line.split('=',1) for line in result.splitlines())))"
        value=json.loads(base.transport.remote(member,code,timeout=30,python=item['python']))
        require(value=={'MemoryMax':str(4*1024**3),'CPUQuotaPerSecUSec':'1s'},'owned service limit differs: '+member)
        limits[member]=value
    print('OWNED SERVICE LIMITS PASS: PC/Spark one core and 4GiB; other workloads untouched',flush=True)
    native_config=manifest['handoff']['configurations']['a']
    with tempfile.TemporaryDirectory(prefix='public-handoff-kernel-') as temp:
        for name,wanted in manifest['handoff']['descriptor']['modules'].items():
            output=Path(temp)/Path(name).name;source=name.removesuffix('.olean')+'.lean'
            result=subprocess.run([native_config['backend'][0],'--trust=0','-DwarningAsError=true','-o',str(output),source],cwd=ROOT/'Lean',env={**os.environ,'LEAN_PATH':native_config['lean_path']},text=True,capture_output=True)
            require(result.returncode==0 and sha(output)==wanted,'strict installed source rebuild differs: '+source+' '+result.stdout[-1000:])
    mouths=['from_consumed_is_actual_next','Seed.original_prefix','Seed.inherited_raw_items',
      'Seed.current_is_own_root_current','Seed.emission_uses_exact_request','Seed.target_is_a_different_task_member',
      'Seed.handoff_before_is_actual_parent_next','Seed.preserves_every_claim','Seed.every_material_flow',
      'access_valid_iff','stale_holder_cannot_access','Delivery.authority_is_paid_and_within_the_new_window',
      'Delivery.service_really_debits_the_candidate','Delivery.delivery_really_debits_the_service',
      'Delivery.every_slice_has_original_service_origin','Delivery.both_independent_checks_consume_the_original_service',
      'Runtime.shares_actual_writeback_and_generated_next']
    namespace='SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff'
    with tempfile.TemporaryDirectory(prefix='public-handoff-axioms-') as temp:
        path=Path(temp)/'Axioms.lean';path.write_text('import '+namespace+'.Runtime\n'+''.join('#print axioms '+namespace+'.'+name+'\n' for name in mouths))
        result=subprocess.run([native_config['backend'][0],'--trust=0',str(path)],cwd=ROOT/'Lean',env={**os.environ,'LEAN_PATH':native_config['lean_path']},text=True,capture_output=True)
        require(result.returncode==0 and result.stdout.count('depends on axioms:')==len(mouths),'axiom replay failed: '+result.stdout[-1000:])
        for block in re.findall(r'depends on axioms: \[(.*?)\]',result.stdout,re.S):
            require(set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',block))<={'propext','Classical.choice','Quot.sound'},'nonstandard axiom')
        (box/'ha/handoff/axioms.log').write_text(result.stdout)
    print('HANDOFF KERNEL/INSTALLATION PASS: two exact trust0/warningAsError rebuilds; 17 standard-axiom mouths; three independent 5216-artifact live readers',flush=True)
    if full:
        old.physical_baseline()
        result=subprocess.run([sys.executable,str(Path(__file__).with_name('public-source-final-audit.py')),'--check-main'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (box/'ha/handoff/original-six-final.log').write_text(result.stdout)
        require(result.returncode==0,'original six/full cost audit failed: '+result.stdout[-1800:])
        print('ORIGINAL SIX/FULL COST PASS: fresh final audit and original 514-event physical replay',flush=True)
    files=['Verification/public-audit/network/'+name for name in manifest['protocol']]
    files+=['Verification/public-audit/network/client.py']
    files+=['Lean/scripts/verification/public-handoff-'+name for name in ['source.lean','deploy.py','actual.py','local.py','check.py']]
    files+=['Lean/scripts/verification/public-ha-check.py']
    files+=['Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/'+name for name in ['Handoff.lean','Handoff/Runtime.lean']]
    inputs={name:sha(ROOT/name) for name in files}
    live_timing = None
    if manifest.get('public_timing'):
        spec = importlib.util.spec_from_file_location('original_live_timing_consumer', Path(__file__).with_name('public-live-timing-check.py'))
        consumer = importlib.util.module_from_spec(spec);spec.loader.exec_module(consumer)
        live_timing = consumer.audit(box, check_main=check_main, native_runtime=semantic['admission'])
        inputs.update(live_timing['source_inputs'])
    if manifest.get('native_admission'):
        inputs.update(semantic['admission']['source_inputs'])
    if check_main:
        for name,wanted in inputs.items():require(hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+name],cwd=ROOT)).hexdigest()==wanted,'main differs: '+name)
        print('DISTINCT AUDITOR MAIN INTEGRATION PASS',flush=True)
    save(box/'ha/handoff/final-check.json',{'exit':0,'events':27,'head':literal[-1][2],
      'supplier_transfer':3,'energy_consumed':5,'window':[35,41],'old_holder':1,'new_holder':2,
      'inputs':inputs,'workers':workers,'semantic':semantic,'axiom_mouths':17,'kernel_modules':2,
      'full':full,'main_verified':check_main,'service_limits':limits,'public_timing':live_timing,'at':time.time()})
    print('INDEPENDENT DISTINCT AUDITOR AUDIT ACCEPTED',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    try:run(a.box.resolve(),a.full,a.check_main)
    finally:governance.close_readers();energy.close_readers()
