from pathlib import Path
import hashlib
import json
import subprocess
import sys

root=Path('runtime/Documents/Homework')
box=Path(__file__).absolute().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipt=load(box/'installation/receipt.json');production=load(box/'production-verification.json')
assert receipt['source_installed'] and receipt['installed_source_recompile']
assert len(receipt['installed'])==39
for p,value in receipt['installed'].items():assert sha(root/p)==value,p
for p,value in receipt['evidence'].items():assert sha(root/p)==value,p
assert sha(root/receipt['installed_validation'])==receipt['installed_validation_sha256']
assert production['strict_modules']==54 and production['direct_contracts']=='75/75' and production['actual_public_two_rounds']=='12/12'
assert production['all_actual_source_snapshots_are_current_production']
prod=box/'production';config=load(prod/'lean-env.json')
for entry in production['compile_records']:
    record=load(entry['receipt']);assert record['exit']==0 and record['exact_dependencies']
    assert record['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000)
    wanted=next((row for row in load(box/'source-plan.json') if row['module']==record['module']),None)
    if wanted and wanted.get('setup'):
        assert sha(wanted['setup'])==wanted['setup_sha256']==record['setup_sha256']
        assert record['module_package']==wanted['package']
    runtime_config=load(box/'lean-env.json')
    setup=runtime_config.get('module_setups',{}).get(record['module'])
    assert config.get('module_setups',{})==runtime_config.get('module_setups',{})
    assert record['module_package']==(load(setup)['package'] if setup else None)
    assert record['setup_sha256']==(sha(setup) if setup else None)
    assert record['source'].startswith('Lean/') and sha(root/record['source'])==record['source_sha256']
    artifact=prod/'lib'/Path(record['module'].replace('.','/')+'.olean')
    assert sha(artifact)==record['artifact_sha256']
    for module,value in record['dependencies'].items():
        relative=Path(module.replace('.','/')+'.olean');path=next(Path(base)/relative for base in config['LEAN_PATH'].split(':') if (Path(base)/relative).exists());assert sha(path)==value
for label,marker in [('installed-default','CONTRACT PASS: 8/8'),('installed-input','PASS: 20/20'),('installed-raw','PASS: 18/18'),('installed-recursion','PASS: 17/17'),('installed-original-reentry','PASS: 12/12')]:
    record=load(prod/(label+'-run.json'));assert record['exit']==0 and marker in record['output']
    assert record['trust']==0 and record['werror'] and not record['elab_async']
    assert sha(root/record['source'])==record['source_sha256']
    for p,value in record['imports'].items():assert sha(p)==value
assert 'INTEGRATED LOGICAL IDENTITY PASS: modules=54;' in (prod/'logical-identity.log').read_text()
for row in load(box/'source-plan.json'):
    target=root/'Lean'/Path(row['module'].replace('.','/')+'.lean') if row['module']!='PublicDefaultActualNative' else root/'Lean/scripts/verification/public-source-owned-iteration-consumer.lean'
    assert sha(target)==row['source_sha256'],str(target)
consumer=load(prod/'installed-consumer-verification.json')
assert consumer['accepted'] and consumer['exit']==0 and consumer['trust']==0 and consumer['werror'] and not consumer['elab_async']
assert consumer['complete_module_c_byte_identical'] and consumer['actual_cases']==12
assert sha(root/consumer['source'])==consumer['source_sha256']==load(box/'actual-run.json')['source_sha256']
assert sha(consumer['artifact'])==consumer['artifact_sha256']
assert sha(consumer['complete_c'])==consumer['complete_c_sha256']==consumer['executed_complete_c_sha256']==sha(box/'generated/PublicDefaultActualNative.c')
assert consumer['reused_actual_receipt_sha256']==sha(box/'actual-run.json')
assert consumer['verification_script_sha256']==sha(box/'certify_installed_consumer.py')
assert production['installed_actual_consumer_verification_sha256']==sha(prod/'installed-consumer-verification.json')
assert 'INTEGRATED LOGICAL IDENTITY PASS: modules=1;' in consumer['identity_output']
for path,value in consumer['imports'].items():assert sha(path)==value
subprocess.run([sys.executable,str(box/'verify_actual.py')],cwd=root,check=True)
subprocess.run([sys.executable,str(box/'verify_linkage.py')],cwd=root,check=True)
record=dict(accepted=True,installed_paths=39,production_strict_modules=54,direct_contracts='75/75',actual_rounds=2,actual_cases=12,actual_receipt_sha256=sha(box/'actual-run.json'),production_verification_sha256=sha(box/'production-verification.json'),goal_complete=False)
(box/'installed-evidence-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('INTEGRATED INSTALLED EVIDENCE PASS: 39 production paths; 54 current source compiles; 75 contracts; original literal actual 12/12; all executed source snapshots match production')
