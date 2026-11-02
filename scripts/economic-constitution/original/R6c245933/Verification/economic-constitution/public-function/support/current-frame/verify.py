from pathlib import Path
import hashlib,json,re
b=Path(__file__).absolute().parent;root=Path('runtime/Documents/Homework');load=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs={}
def keep(path):
 path=Path(path);inputs[str(path)]=sha(path);return path
for label in ['StandaloneCurrentFrame','RepairCurrentFrame']:
 rec=load(keep(b/(label+'-compile.json')))
 assert rec['exit']==0 and rec['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000)
 assert sha(keep(root/rec['source']))==rec['source_sha256']
 assert sha(keep(rec['c_path']))==rec['c_sha256']
 artifact=b/'lib'/Path(rec['module'].replace('.','/')+'.olean');assert sha(keep(artifact))==rec['artifact_sha256']
core=next(r for r in load(b.parent/'native/original-project-inputs.json') if r['module']=='SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingExecution')
assert sha(keep(b/'lib/SaturationMonoid/ProcessGame/Society/PublicFunction/OutstandingExecution.olean'))==core['input_olean_sha256']
identity=load(keep(b/'identity-consumer-run.json'));assert identity['exit']==0
assert 'unchangedOriginalBodiesAndTypes=41; additiveDeclarations=0' in identity['output']
assert sha(keep(root/identity['source']))==identity['source_sha256']
for original,candidate in [identity['arguments'][i:i+2] for i in range(0,len(identity['arguments']),2)]:keep(original);keep(candidate)
kernel=load(keep(b/'current-kernel-run.json'));assert kernel['exit']==0 and 'roots=2, closure=3454, private=364, axioms=[Quot.sound, Classical.choice, propext]' in kernel['output']
assert sha(keep(root/kernel['source']))==kernel['source_sha256']
ir=load(keep(b/'current-ir-run.json'));assert ir['exit']==0 and sha(keep(root/ir['source']))==ir['source_sha256']
for rec in [identity,kernel,ir]:
 for path,digest in rec['imports'].items():assert sha(keep(path))==digest
entries=load(keep(b/'ir.json'));body=next(r['body'] for r in entries if r['name']=='SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair.actualAt')
assert 'OutstandingSource.frameCurrentAt._at_' in body and 'ProgrammeHistory.visitAt' not in body
candidate=Path(load(b/'RepairCurrentFrame-compile.json')['c_path']);text=candidate.read_text()
assert 'OutstandingSource_frameCurrentAt___at___' in text
assert 'ProgrammeHistory_visitAt___at___00SaturationMonoid_ProcessGame_Society_PublicFunction_OutstandingSource_currentAt' not in text
plan=load(keep(b/'refresh-plan.json'));assert sha(keep(plan['original_c']))==plan['original_c_sha256'] and sha(keep(plan['candidate_c']))==plan['candidate_c_sha256']
assert len(plan['external_callers'])==26 and len(plan['removed_or_changed_symbols'])==157
keep(b/'verify.py');keep(b/'source-bindings.json')
record=dict(certified=True,kind='same-occurrence raw current readout',strict_modules=2,original_repair_declarations=41,original_core_artifact_unchanged=True,complete_function_equality=True,fresh_empty_environment_kernel=True,kernel_roots=2,kernel_closure=3454,kernel_private=364,standard_three_axioms=True,original_actualAt_ir_consumes_frame=True,old_sampled_visit_removed_from_owner=True,exact_external_c_callers=26,registered_actual_route=False,installed=False,inputs=inputs)
(b/'verification-check.json').write_text(json.dumps(record,indent=2)+'\n')
print('CURRENT FRAME READOUT PASS: 2 strict modules; 41 original Repair types/bodies unchanged; original core artifact identical; complete function equality')
print('CURRENT FRAME CONSUMER PASS: original actualAt IR/C reads the same frame; sampled visit helper removed; empty kernel 2/3454/364, standard three axioms; 26 exact external callers require refresh')
