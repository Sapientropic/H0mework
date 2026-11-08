"""Independent original18, native source, two-account cost and physical quorum audit."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from crypto import verify
from recovery_loop import save
from source_semantics import Engine
from service import Store
import governance
import energy


def module(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


old=module('energy_inherited_governance','public-governance-check.py')
base=old.base;require=base.require;load=base.load;sha=base.sha


def native_workers(box,manifest,current):
    return old.runtime(box,manifest,current,feature='energy',expected_files=5212)


def run(box,full,check_main):
    manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service'];original=load(box/'service.json')
    current_rows=base.database(Path(cfg['database']));literal=current_rows['rows']
    case=box/'ha/energy/actual-01';prefix=load(box/'ha/governance/actual-01/after.json')['rows']
    require(len(literal)==18 and literal[:16]==[tuple(row) for row in prefix],'original16 prefix or expected actual18 differs')
    validator=object.__new__(Store);validator.config=cfg;validator.anchor=object()
    class PublicSigner:
        def public_key(self):return public_key(cfg['registry']['server'])
    validator.key=PublicSigner();validator.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:validator.validate_ledger();validator.validate_anchor_receipts()
    finally:validator.database.close()
    engine=Engine({**manifest['semantic']['configurations']['a'],'replay_seconds':120,
                   'error_log':str(box/'ha/energy/independent-source.log')})
    try:engine.sync(literal)
    finally:engine.close()
    first=json.loads(literal[16][3])['body'];second=json.loads(literal[17][3])['body']
    for number,event in [(16,first),(17,second)]:
        checked=energy.expected(cfg,literal[:number],event)
        count=6 if number==16 else 1
        require(checked==[{'payment':['verified']*count,'lifecycle':['verified']*count}], 'dual service consumers differ')
        require(event['native']['scope']=={'unit':'energy','earliest':'26','deadline':'32','slots':6,
                'revisionEnergy':'1','oldDeadline':'22'},'source-generated scope differs')
        require(all(value=='0' for value in event['native']['epoch']['next']['labor']),'old labor credited')
    require(first['native']['supply']['before']['energy']==['8','0','0','12'] and
            first['native']['epoch']['next']['energy']==['8','1','0','6'] and
            second['native']['epoch']['next']['energy']==['7','0','0','6'], 'full energy costs differ')
    for tag,row in [('renewal',literal[16]),('audit',literal[17])]:
        result=load(case/(tag+'-result.json'))
        require(result['ledger']==json.loads(row[3]) and result['anchor']['body']['seq']==row[0],'actual client delivery differs')
        lookup=load(case/(tag+'-lookup.json'))
        require(lookup['body']['result']['ledger']==result['ledger'],'original request lookup changed payment')
    require(len(load(box.parent/'mandate/energy-controls-final-v3/accepted.json')['tests'])==18,'source controls absent')
    require(len(load(box.parent/'mandate/energy-semantic-controls-03/acceptance.json')['tests'])==16,'slow source/CAS controls absent')
    print('INDEPENDENT ORIGINAL18 PASS: original16 unchanged; supplier6; application1 + grant2 + service/delivery4; labor0; two original-service consumers; lookup without repeat payment',flush=True)
    current=base.collect(box,manifest)
    node=base.transport.node('b')
    script="$v=(Get-CimInstance Win32_OperatingSystem).LastBootUpTime\n[DateTimeOffset]::new($v).ToUnixTimeSeconds()\n"
    result=node._run_remote([*node.ssh,'powershell','-NoProfile','-Command','-'],input=script.encode(),capture_output=True,timeout=30,allow_probe=False)
    require(result.returncode==0,'Windows boot read unavailable');current['b']['windows_boot_unix']=int(result.stdout.decode().strip())
    base.check_fault(box,manifest,original,literal);base.check_overlap(box,manifest)
    base.module('energy_alternating','public-ha-alternating-check.py').check(box,manifest,original,literal[:13])
    base.check_current(box,manifest,original,current_rows,current)
    semantic=base.module('energy_semantic','public-semantic-check.py').check(box,manifest,original,literal,current)
    governance_workers=old.runtime(box,manifest,current);workers=native_workers(box,manifest,current)
    # Rebuild only the two new source modules; require exact installed artifacts.
    with tempfile.TemporaryDirectory(prefix='public-energy-kernel-') as temp:
        for name,wanted in manifest['energy']['descriptor']['modules'].items():
            source=name.removesuffix('.olean')+'.lean';output=Path(temp)/Path(name).name
            native_config=manifest['energy']['configurations']['a']
            result=subprocess.run([native_config['backend'][0],'--trust=0','-o',str(output),source],cwd=ROOT/'Lean',env={**os.environ,'LEAN_PATH':native_config['lean_path']},text=True,capture_output=True)
            require(result.returncode==0 and sha(output)==wanted,'installed artifact is not the strict source rebuild: '+source+' '+result.stdout[-800:])
    mouths=['original_prefix','actual_supply_next','refusal_has_an_actual_reason','task_homology',
      'Ready.epoch_has_exact_actual_initial','Ready.epoch_is_own_root_current','Ready.epoch_preserves_claims',
      'Ready.every_stock_flow_is_accounted','Delivery.authority_is_paid_and_within_the_new_window',
      'Delivery.service_really_debits_the_candidate','Delivery.delivery_really_debits_the_service',
      'Delivery.both_independent_checks_consume_the_original_service','Runtime.shares_actual_writeback_and_generated_next',
      'before_is_the_original_governance_cut','inherited_raw_items','supply_is_the_roots_actual_word',
      'Ready.original_finance_matrix','Runtime.EpochSeed.starts_at_the_supply_roots_generated_next',
      'Runtime.EpochSeed.preserves_owner_roles_and_original_failures']
    namespace='SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal'
    with tempfile.TemporaryDirectory(prefix='public-energy-axioms-') as temp:
        mouth_file=Path(temp)/'Mouths.lean'
        mouth_file.write_text('import '+namespace+'.Runtime\n'+''.join('#print axioms '+namespace+'.'+name+'\n' for name in mouths))
        result=subprocess.run([native_config['backend'][0],'--trust=0',str(mouth_file)],cwd=ROOT/'Lean',env={**os.environ,'LEAN_PATH':native_config['lean_path']},text=True,capture_output=True)
        require(result.returncode==0 and result.stdout.count('depends on axioms:')==len(mouths),'axiom mouth replay failed')
        import re
        for block in re.findall(r'depends on axioms: \[(.*?)\]',result.stdout,re.S):
            require(set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',block)) <= {'propext','Classical.choice','Quot.sound'},'nonstandard axiom')
        (box/'ha/energy/axioms.log').write_text(result.stdout)
    print('ENERGY KERNEL/INSTALLATION PASS: two exact trust0 rebuilds; 19 axiom mouths; three live independent 5212-artifact readers; inherited 5210 readers retained',flush=True)
    if full:
        old.physical_baseline()
        result=subprocess.run([sys.executable,str(Path(__file__).with_name('public-source-final-audit.py')),'--check-main'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (box/'ha/energy/original-six-final.log').write_text(result.stdout)
        require(result.returncode==0,'original six/full cost audit failed: '+result.stdout[-1800:])
        print('ORIGINAL SIX/FULL COST PASS: fresh final audit and original 514-event physical replay',flush=True)
    files=['Verification/public-audit/network/'+name for name in manifest['protocol']]
    files+=['Verification/public-audit/network/client.py']
    files+=['Lean/scripts/verification/public-energy-'+name for name in ['source.lean','deploy.py','actual.py','local.py','check.py']]
    files+=['Lean/scripts/verification/'+name for name in ['public-ha-check.py','public-governance-check.py','public-ha-deploy.py','public-semantic-local.py','public-semantic-check.py']]
    files+=['Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/'+name
            for name in ['EnergyRenewal.lean','EnergyRenewal/Runtime.lean']]
    inputs={name:sha(ROOT/name) for name in files}
    if check_main:
        for name,wanted in inputs.items():require(hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+name],cwd=ROOT)).hexdigest()==wanted,'main differs: '+name)
        print('ENERGY EPOCH MAIN INTEGRATION PASS',flush=True)
    save(box/'ha/energy/final-check.json',{'exit':0,'events':18,'head':literal[-1][2],
         'energy_consumed':7,'supplier_transfer':6,'labor_balance':0,'old_deadline':22,'new_window':[26,32],
         'inputs':inputs,'workers':workers,'governance_workers':governance_workers,'semantic':semantic,
         'axiom_mouths':len(mouths),'kernel_modules':2,'full':full,'main_verified':check_main,'at':time.time()})
    print('INDEPENDENT PAID ENERGY SCOPE AUDIT ACCEPTED',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    try:run(a.box.resolve(),a.full,a.check_main)
    finally:governance.close_readers();energy.close_readers()
