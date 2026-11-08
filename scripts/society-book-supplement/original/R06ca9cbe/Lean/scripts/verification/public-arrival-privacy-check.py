"""Consume the universal arrival privacy proofs and the original online literal."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from crypto import digest
from recovery_loop import save

BASE='SaturationMonoid.ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Regeneration/Supply/Material/Productive/ExternalArrival'.replace('/','.')
INSTRUMENT='SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.InstrumentProjection'
MODULES=[BASE+'.'+name for name in ('ArrivalBisimulation','ArrivalBisimulationConsumer',
    'ArrivalBisimulationControls','FinancialProjection','ArrivalSlotHistory','ArrivalDeliveryLedger',
    'ArrivalWirePrivacy','ArrivalWireConsumer','AdaptivePrivacy')]+[INSTRUMENT]
NAMESPACE=BASE.replace('.Supply.Material.Productive.','.Supply.Productive.')
MOUTHS=[NAMESPACE+'.'+name for name in (
    'Runtime.source_input_is_the_complete_actual_source','Runtime.same_occurrence_whole_ledger_and_own_next',
    'Consume.actual_source_and_customer_material_commute','ArrivalWirePrivacy.original_source_generates_the_wire_relation',
    'ArrivalWirePrivacy.complete_original_wire_outputs_are_equal','ArrivalWirePrivacy.original_public_readout_is_its_actual_branch',
    'AdaptivePrivacy.original_source_generates_every_adaptive_complete_output','AdaptivePrivacy.original_source_generates_equal_adaptive_outputs',
    'AdaptivePrivacy.every_adaptive_prefix_has_equal_complete_output_and_related_own_next',
    'AdaptivePrivacy.every_generated_strategy_run_keeps_its_own_responsibility',
    'AdaptivePrivacy.every_generated_strategy_run_is_consumed_by_the_original_execute',
    'AdaptivePrivacy.the_original_public_readout_consumes_the_generated_strategy_run',
    'AdaptivePrivacy.every_adaptive_suffix_keeps_the_same_consumed_source','AdaptivePrivacy.zero_steps_do_not_report_a_service_decision',
    'ArrivalWireConsumer.the_actual_fresh_arrival_is_distinct_from_blocked',
    'ArrivalWireConsumer.replay_is_blocked_without_a_new_source_debit','ArrivalWireConsumer.malformed_input_keeps_the_entire_state',
    'ArrivalWireConsumer.deleting_the_source_prevents_execution',
    'ArrivalWireConsumer.the_full_public_state_json_does_not_reconstruct_the_private_current')]
FLAGS=['--trust=0','-j1','-DElab.async=false','-DwarningAsError=true']


def load(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def location(box):return box/'ha/regeneration/productive/external-arrival/online/privacy-universal'


def verify(box,check_main=False):
    home=location(box);online=home.parent;settings=load(box/'ha/deployment.json')['mac']['service']['arrival']
    setup=load(home/'setup.json');inputs={};artifacts={}
    for module in MODULES:
        source=ROOT/'Lean'/Path(module.replace('.','/')+'.lean');receipt=load(home/(module.rsplit('.',1)[-1]+'.json'))
        assert receipt['exit']==0 and receipt['source']==sha(source),('PROOF_SOURCE_CHANGED',module)
        assert all(flag in receipt['command'] for flag in FLAGS),('PROOF_TRUST_FLAGS',module)
        artifact=Path(setup['importArts'][module][0][0]);assert sha(artifact)==receipt['artifact']
        inputs[str(source.relative_to(ROOT))]=sha(source);artifacts[module]=sha(artifact)
    # The proof consumes the same Wire module selected by the installed source.
    wire=BASE+'.Wire';selected=Path(setup['importArts'][wire][0][0]);inventory=load(settings['closure'])
    assert sha(selected)==inventory[wire.replace('.','/')+'.olean']
    assert sha(settings['closure'])==settings['descriptor']['closure_sha256']
    environment=load(home/'environment.json');tool=environment['tool']
    prefix=subprocess.check_output([tool,'--print-prefix'],text=True).strip()
    lean_path=str(Path(prefix)/'lib/lean')+':'+environment['lean_path']
    execution_artifacts={**artifacts,wire:sha(selected)}

    def bound_execution(receipt,setup_name,source,run=False):
        selected_setup=home/setup_name
        assert receipt['source']==sha(source) and receipt['setup_sha256']==sha(selected_setup)
        assert receipt['tool_sha256']==sha(tool) and receipt['lean_path']==lean_path
        assert receipt['artifacts']==execution_artifacts
        command=[tool,*FLAGS,'--setup='+str(selected_setup)]
        if run:command.append('--run')
        command.append(str(source.relative_to(ROOT/'Lean')))
        assert receipt['command']==command,('EXECUTION_COMMAND_CHANGED',source.name)
        for module,wanted in execution_artifacts.items():
            assert sha(load(selected_setup)['importArts'][module][0][0])==wanted

    kernel=load(home/'kernel.json');axioms=load(home/'axioms.json')
    assert kernel['exit']==axioms['exit']==0
    kernel_source=Path(__file__).with_name('public-arrival-privacy-kernel.lean')
    bound_execution(kernel,'kernel-setup.json',kernel_source)
    assert kernel['source']==sha(kernel_source) and kernel['log_sha256']==sha(home/'kernel.log')
    assert kernel['stderr_sha256']==sha(home/'kernel.stderr') and not (home/'kernel.stderr').read_text()
    stats=re.search(r'KERNEL REPLAY PASS: roots=(\d+), closure=(\d+), private=(\d+), axioms=\[([^\]]*)\]',(home/'kernel.log').read_text(),re.S)
    assert stats and int(stats[1])==len(MOUTHS) and int(stats[2])>0
    allowed={'propext','Classical.choice','Quot.sound'}
    kernel_axioms=set(stats[4].replace('\n','').replace(' ','').split(','))-{''}
    assert kernel_axioms<=allowed
    assert axioms['source']==sha(home/'Axioms.lean') and axioms['log_sha256']==sha(home/'axioms.log')
    found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(home/'axioms.log').read_text(),re.S)
    assert [name for name,_ in found]==MOUTHS
    actual_axioms=set()
    for _,axiom_list in found:
        current=set(axiom_list.replace('\n','').replace(' ','').split(','))-{''}
        assert current<=allowed
        actual_axioms.update(current)
    assert actual_axioms==kernel_axioms
    # Keep the exact setup and artifacts used by the empty-environment replay.
    kernel_setup=load(home/'kernel-setup.json')
    for module,wanted in artifacts.items():assert sha(kernel_setup['importArts'][module][0][0])==wanted
    source=Path(__file__).with_name('public-arrival-privacy-source.lean')
    compiled=load(home/'source-compile.json');native=load(home/'public-native.json')
    bound_execution(native,'source-setup.json',source,run=True)
    assert compiled['exit']==native['exit']==0 and compiled['source']==native['source']==sha(source)
    assert native['input']==sha(home/'public-input.json') and native['output']==sha(home/'public-output.json')
    assert native['stderr_sha256']==sha(home/'public-native.stderr') and not (home/'public-native.stderr').read_text()
    argument=load(home/'public-input.json');output=load(home/'public-output.json');rows=load(online/'actual/events.json')
    assert len(rows)==77 and argument==dict(source=load(online/'actual/source-input.json')['source'],steps=8)
    events=[json.loads(row[3])['body'] for row in rows[69:]]
    assert output['events']==[event['request']['body']['command'] for event in events]
    assert output['output']==[event['native'] for event in events]
    assert output['request']==dict(source=argument['source'],events=output['events'])
    assert output['differentHistoryCommand']==dict(kind='unexpected-history',index=1)
    assert [v['status'] for v in output['output']]==['BLOCKED','ARRIVED','OPENED','BLOCKED','DELIVERED','ERROR','ERROR','BLOCKED']
    live=load(online/'final-check.json');assert live['exit']==0 and live['events']==77 and live['head']==rows[-1][2]
    assert live['replicas']==dict.fromkeys('abcd',77) and live['arrival']['outstanding']=='0'
    assert load(online/'actual/owner-accepted.json')['frames']==['39','38']
    for path in [Path(__file__),kernel_source,source]:inputs[str(path.relative_to(ROOT))]=sha(path)
    acceptance=ROOT/'Verification/public-audit/regeneration/productive/arrival-privacy.json'
    certificate=load(acceptance)
    assert certificate['modules']==len(MODULES) and certificate['mouths']==MOUTHS
    assert certificate['inputs']==inputs and certificate['artifacts']==artifacts
    for path,wanted in certificate['receipts'].items():assert sha(home/path)==wanted
    inputs[str(acceptance.relative_to(ROOT))]=sha(acceptance)
    for path,wanted in inputs.items():
        if check_main:
            assert hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+path],cwd=ROOT)).hexdigest()==wanted,('MAIN_SOURCE_CHANGED',path)
    report=dict(exit=0,modules=len(MODULES),mouths=len(MOUTHS),kernel_closure=int(stats[2]),
        private_declarations=int(stats[3]),axioms=sorted(actual_axioms),universal_json_words=True,
        arbitrary_public_history_strategies=True,actual_wire_consumer=True,source_generated_initialization=True,
        private_frame_and_financial_origins_retained=True,consumed_source_cannot_reopen=True,
        exact_execution_configuration=True,strict_source_execution=True,
        actual_events=77,literal_replies=8,source=digest(argument['source']),installed_wire=sha(selected),
        inputs=inputs,artifacts=artifacts,main_verified=check_main)
    save(home/'independent.json',report)
    print('ARRIVAL UNIVERSAL PRIVACY PASS: arbitrary JSON words and public-history adaptive policies; actual Wire.execute/publicReadout; own next, private frames, financial origins, spent source',flush=True)
    print('INDEPENDENT KERNEL PASS: '+str(len(MOUTHS))+' mouths; '+str(stats[2])+' declarations; axioms='+', '.join(sorted(actual_axioms)),flush=True)
    print('ADAPTIVE ORIGINAL77 LITERAL PASS: 8 exact replies; zero new economic event; main_verified='+str(check_main).lower(),flush=True)
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--check-main',action='store_true');a=p.parse_args();verify(a.box.resolve(),a.check_main)
