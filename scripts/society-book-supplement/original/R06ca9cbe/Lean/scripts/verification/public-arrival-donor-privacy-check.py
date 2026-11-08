"""Consume exact donor-composition proof receipts; never regenerate a source or event."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'Verification/public-audit/network'))
from recovery_loop import save
from crypto import digest, verify as verify_signature
from anchor import public_key
import donor_arrival_admission

BASE = 'SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive'
MODULES = [BASE+'.DonorRelease']+[BASE+'.ExternalArrival.Donor.'+name for name in
    ('Source','Consumer','Wire','Privacy.SourceFunding','Privacy')]
NAMESPACE = BASE.replace('.Material.Productive','.Productive')+'.ExternalArrival.Donor'
MOUTHS = [NAMESPACE+'.'+name for name in (
    'Runtime.same_occurrence_whole_ledger_and_own_next','Consumer.the_same_actual_occurrence_pays_and_delivers',
    'Consumer.a_new_donor_never_reopens_the_old_complete_source','Consumer.the_whole_old_responsibility_and_financial_prefix_survive',
    'Wire.every_old_command_uses_the_original_consumer','Privacy.SourceFunding.original_governance_generates_its_private_feed_range',
    'Privacy.SourceFunding.actual_source_initial_is_backed','Privacy.SourceFunding.original_arrival_execution_is_backed',
    'Privacy.donate_related','Privacy.render_public','Privacy.original_base_generates_the_donor_initial_relation',
    'Privacy.original_source_generates_the_complete_donor_execution_relation','Privacy.complete_original_donor_readouts_are_equal',
    'Privacy.every_adaptive_prefix_keeps_related_actual_successors_and_complete_output',
    'Privacy.the_original_source_generates_every_adaptive_donor_relation',
    'Privacy.every_generated_policy_word_is_consumed_by_the_original_wire')]
FLAGS = ['--trust=0','-j1','-DElab.async=false','-DwarningAsError=true']


def load(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify(box, check_main=False, profile='producer'):
    base=box/'ha/regeneration/productive/external-arrival/online/donor-privacy'
    directory=base/'producer' if profile=='producer' else base
    setup=load(directory/'setup.json');environment=load(directory/'environment.json')
    sources={};artifacts={}
    actual=load(load(directory/'producer-profile.json')['source']) if profile=='producer' else None
    work=Path(load(directory/'producer-profile.json')['source']).parents[1] if actual else None
    program=load(work/'program.json') if actual else None
    votes=load(work/'votes.json') if actual else None
    producer_sources={}
    if actual:
        selected_profile=load(directory/'producer-profile.json')
        assert sha(selected_profile['source'])==selected_profile['source_sha256']
        assert actual['member']=='a' and actual['actual_setup'] is None
        for name,selection in actual['importArts'].items():
            assert setup['importArts'][name]==selection,('PRODUCER_IMPORT_REPLACED',name)
        settings=load(box/'ha/deployment.json')['mac']['service']['arrival']
        assert actual['baseline_closure_sha256']==sha(actual['baseline_closure'])==settings['descriptor']['closure_sha256']
        rows=load(box/'ha/regeneration/productive/external-arrival/online/actual/events.json')
        config=load(box/'local-anchor/config.json')
        point=donor_arrival_admission.permission(config,rows,program,votes,load(work/'owner-permit.json'))
        assert point['prefix']==dict(seq=77,head=rows[-1][2]) and point['history']==digest(rows)
        assert actual['point']==digest(point)
        for member in 'abcd':
            peer=load(Path(selected_profile['source']).with_name('actual-'+member+'.json'))
            evidence=load(work/('evidence-'+member+'.json'))
            signed=verify_signature(public_key(config['ha']['trust']['members'][member]),donor_arrival_admission.READY,votes[member])
            assert signed['point']==point and signed['member']==member
            assert peer['point']==actual['point'] and peer['source_commit']==actual['source_commit']
            assert signed['objects']==peer['own_objects']==actual['own_objects']==evidence['objects']==evidence['native']['objects']
            assert evidence['native']['exit']==0 and all(flag in evidence['native']['strict'] for flag in FLAGS)
            assert evidence['native']['input']==signed['input']==digest(evidence['input'])
            assert evidence['native']['output']==signed['output']==digest(evidence['output'])
            assert evidence['input']==load(work/'request.json') and evidence['native']['program']==program
        # Bind the actual exporter and its consumer too: a matching module name is
        # insufficient when a worker may have executed a different entrypoint.
        for key,recorded in program['sources'].items():
            source=ROOT/'Lean'/key
            frozen=subprocess.check_output(['git','show',actual['source_commit']+':Lean/'+key],cwd=ROOT)
            assert sha(source)==recorded==hashlib.sha256(frozen).hexdigest(),('PRODUCER_SOURCE_CHANGED',key)
            producer_sources[str(source.relative_to(ROOT))]=recorded
        auth_source=ROOT/'Verification/public-audit/network/donor_arrival_admission.py'
        producer_sources[str(auth_source.relative_to(ROOT))]=sha(auth_source)
        for module in MODULES[:4]:
            source=ROOT/'Lean'/Path(module.replace('.','/')+'.lean');key=module.replace('.','/')
            recorded=program['sources'][key+'.lean']
            frozen=subprocess.check_output(['git','show',actual['source_commit']+':Lean/'+key+'.lean'],cwd=ROOT)
            assert sha(source)==recorded==hashlib.sha256(frozen).hexdigest()
            artifact=setup['importArts'][module][0][0]
            assert sha(artifact)==actual['own_objects'][key+'.olean']
            sources[str(source.relative_to(ROOT))]=recorded;artifacts[module]=sha(artifact)
    for module in (MODULES[4:] if actual else MODULES):
        source=ROOT/'Lean'/Path(module.replace('.','/')+'.lean')
        receipt=load(directory/(module.rsplit('.',1)[-1]+'.json'))
        assert receipt['exit']==0 and receipt['source']==sha(source),('SOURCE_CHANGED',module)
        assert all(flag in receipt['command'] for flag in FLAGS),('STRICT_FLAGS',module)
        artifact=Path(setup['importArts'][module][0][0]);assert sha(artifact)==receipt['artifact']
        assert receipt['setup_sha256']==sha(directory/(module.rsplit('.',1)[-1]+'-setup.json'))
        for dependency,wanted in receipt['imports'].items():
            assert sha(setup['importArts'][dependency][0][0])==wanted,('IMPORT_CHANGED',module,dependency)
        assert receipt['log_sha256']==sha(directory/(module.rsplit('.',1)[-1]+'.log'))
        sources[str(source.relative_to(ROOT))]=sha(source);artifacts[module]=sha(artifact)
    # The legacy consumer remains the original admitted source, with its own immutable inventory.
    settings=load(box/'ha/deployment.json')['mac']['service']['arrival'];inventory=load(settings['closure'])
    legacy=BASE+'.ExternalArrival.Wire';legacy_artifact=Path(setup['importArts'][legacy][0][0])
    assert sha(settings['closure'])==settings['descriptor']['closure_sha256']
    assert sha(legacy_artifact)==inventory[legacy.replace('.','/')+'.olean']
    tool=environment['tool'];prefix=subprocess.check_output([tool,'--print-prefix'],text=True).strip()
    lean_path=str(Path(prefix)/'lib/lean')+':'+environment['lean_path']
    kernel_source=Path(__file__).with_name('public-arrival-donor-privacy-kernel.lean')
    for name,source in [('kernel',kernel_source),('axioms',directory/'Axioms.lean')]:
        receipt=load(directory/(name+'.json'));context=directory/(name+'-setup.json');selected=load(context)
        assert receipt['exit']==0 and receipt['source']==sha(source)
        assert receipt['setup_sha256']==sha(context) and receipt['tool_sha256']==sha(tool)
        assert receipt['lean_path']==lean_path and receipt['sources']==sources and receipt['artifacts']==artifacts
        argument=str(source.relative_to(ROOT/'Lean')) if source.is_relative_to(ROOT/'Lean') else str(source)
        assert receipt['command']==[tool,*FLAGS,'--setup='+str(context),argument]
        for module,wanted in artifacts.items():assert sha(selected['importArts'][module][0][0])==wanted
        assert sha(selected['importArts'][legacy][0][0])==sha(legacy_artifact)
        assert receipt['log_sha256']==sha(directory/(name+'.log'))
        assert receipt['stderr_sha256']==sha(directory/(name+'.stderr')) and not (directory/(name+'.stderr')).read_text()
    stats=re.search(r'DONOR KERNEL REPLAY PASS: roots=(\d+), closure=(\d+), private=(\d+), axioms=\[([^\]]*)\]',
        (directory/'kernel.log').read_text())
    assert stats and int(stats[1])==len(MOUTHS) and int(stats[2])>0
    allowed={'propext','Classical.choice','Quot.sound'}
    kernel_axioms=set(stats[4].replace(' ','').split(','))-{''};assert kernel_axioms<=allowed
    found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(directory/'axioms.log').read_text(),re.S)
    assert [mouth for mouth,_ in found]==MOUTHS
    actual_axioms=set()
    for _,values in found:
        current=set(values.replace('\n','').replace(' ','').split(','))-{''}
        assert current<=allowed;actual_axioms.update(current)
    assert actual_axioms==kernel_axioms
    inputs={**sources,**producer_sources,**{str(path.relative_to(ROOT)):sha(path) for path in (Path(__file__),kernel_source)}}
    acceptance=ROOT/'Verification/public-audit/regeneration/productive/arrival-donor-privacy.json'
    if actual and (acceptance.exists() or check_main):
        frozen=load(acceptance)
        assert frozen['inputs']==inputs and frozen['artifacts']==artifacts
        assert frozen['mouths']==MOUTHS and frozen['kernel_closure']==int(stats[2])
        assert frozen['private_declarations']==int(stats[3]) and frozen['axioms']==sorted(actual_axioms)
        assert frozen['producer_checkpoint']==actual['source_commit']
        for name,wanted in frozen['receipts'].items():assert sha(directory/name)==wanted,('FROZEN_RECEIPT_CHANGED',name)
        for name,wanted in frozen['producer_evidence'].items():assert sha(work/name)==wanted,('FROZEN_PRODUCER_EVIDENCE_CHANGED',name)
    if check_main:
        for path,wanted in inputs.items():
            assert hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+path],cwd=ROOT)).hexdigest()==wanted,('MAIN_SOURCE_CHANGED',path)
    report=dict(exit=0,modules=len(MODULES),mouths=len(MOUTHS),kernel_closure=int(stats[2]),private_declarations=int(stats[3]),
        axioms=sorted(actual_axioms),source_generated_capacity=True,arbitrary_json_words=True,
        arbitrary_public_history_strategies=True,original_wire_consumer=True,own_successors_and_private_residues=True,
        original_claims_and_spent_source_retained=True,inputs=inputs,artifacts=artifacts,main_verified=check_main,
        profile=profile,actual_producer_objects=bool(actual),four_native_members=list('abcd') if actual else [],
        producer_checkpoint=actual['source_commit'] if actual else None)
    save(directory/'independent.json',report)
    print('SOURCE-GENERATED DONOR CAPACITY PASS: all original inputs; own feed 38..40; no caller-funded premise',flush=True)
    print('DONOR COMPOSITION PRIVACY PASS: arbitrary JSON words and public-history policies; original Wire consumer; own successors and private residues',flush=True)
    print('INDEPENDENT DONOR KERNEL PASS: '+str(len(MOUTHS))+' mouths; '+str(stats[2])+' declarations; axioms='+', '.join(sorted(actual_axioms)),flush=True)
    print('DONOR PROOF SOURCE BINDING PASS: six exact modules; profile='+profile+'; main_verified='+str(check_main).lower(),flush=True)
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path);parser.add_argument('--check-main',action='store_true')
    parser.add_argument('--profile',choices=('producer','candidate'),default='producer')
    args=parser.parse_args();verify(args.box.resolve(),args.check_main,args.profile)
