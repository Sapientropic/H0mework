from pathlib import Path
import ast
import hashlib
import json
import os
import re
import shlex
import subprocess
import time

root=Path('runtime/Documents/Homework')
box=Path(__file__).absolute().parent
base=box.parents[1]
shared=base/'shared-runtime'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
inputs={}
def bind(p,wanted=None):
    p=Path(p); value=sha(p)
    assert wanted is None or value==wanted,str(p)
    inputs[str(p)]=value
    return value

state=load(box/'assembly-status.json')
assert state['phase']=='initialization pending independent symbol verification'
old=load(shared/'ready-verification.json')
assert old['ready'] and old['source_compiled_modules']==119
for p,wanted in old['inputs'].items():bind(p,wanted)
bind(shared/'ready-verification.json')
config=load(box/'lean-env.json')
plan=load(box/'source-plan.json');assert len(plan)==121
for name in ['lean-env.json','source-plan.json','source-binding.json','extra-exports-plan.json',
             'assemble.py','verify_ready.py','linked-identity.lean','identity.lean','ir.lean','ir.json',
             'c-sources.json','objects.rsp','check_c_abi.py']:
    bind(box/name)
identity=load(box/'linked-identity.json')
assert identity['exit']==0 and 'INTEGRATED LOGICAL IDENTITY PASS: modules=4;' in identity['output']
bind(box/'linked-identity.json')
kernel=load(box.parent/'direct-kernel-run.json')
assert kernel['exit']==0 and kernel['trust']==0 and kernel['werror'] and not kernel['elab_async']
assert 'roots=120, closure=14594, private=1322' in kernel['output']
bind(box.parent/'direct-kernel-run.json');bind(root/kernel['source'],kernel['source_sha256'])
for p,wanted in kernel['imports'].items():bind(p,wanted)
for label in ['DirectCompletion','DirectReplacement','DirectEvent']:
    path=box/(label+'-compile.json');r=load(path);bind(path)
    assert r['exit']==0 and r['exact_dependencies']
    assert r['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000)
    bind(root/r['source'],r['source_sha256'])
    bind(box/'lib'/Path(r['module'].replace('.','/')+'.olean'),r['artifact_sha256'])
    c=Path(r['c_path']);bind(c,r['c_sha256'])
    for name,wanted in r['dependencies'].items():
        relative=Path(name.replace('.','/')+'.olean')
        p=next(Path(p)/relative for p in config['LEAN_PATH'].split(':') if (Path(p)/relative).exists())
        bind(p,wanted)
    paid=load(box/('object-'+c.stem+'.json'))
    assert paid['exit']==0 and paid['c_sha256']==sha(c)
    bind(c.with_suffix('.o'),paid['object_sha256']);bind(box/('object-'+c.stem+'.json'))
    before=next(item for item in load(base/'native/module-inventory-checked.json') if item['module']==r['module'])
    assert before['package'] is None
    marker='LEAN_EXPORT lean_object* '+before['initializer']+'(uint8_t builtin) {'
    code=c.read_text();assert code.count(marker)==1
    calls=re.findall(r'res = (initialize_\w+)\(builtin\)',code.split(marker,1)[1])
    expected_imports=list(before['import_initializers'])
    if before['is_module']:expected_imports += [before['runtime_initializer'],before['comptime_initializer']]
    assert calls==expected_imports
ir=load(box/'direct-runtime-ir-run.json')
assert ir['exit']==0 and ir['trust']==0 and ir['werror'] and not ir['elab_async']
bind(box/'direct-runtime-ir-run.json');bind(root/ir['source'],ir['source_sha256'])
for p,wanted in ir['imports'].items():bind(p,wanted)
rendered=load(box/'ir.json')
direct=next(r['body'] for r in rendered if r['name'].endswith('Decision.financialRunDirect'))
consumer=next(r['body'] for r in rendered if r['name'].endswith('Disposition.financialRun'))
assert 'Decision.financialRunDirect ' in consumer
assert 'World.handoffFinancialRun ' in direct
assert 'World.generate ' not in direct and 'World.handoff ' not in direct
preflight=load(box/'c-abi-verification.json')
assert preflight['accepted'] and preflight['executable_not_invoked']
sources=[Path(p) for p in load(box/'c-sources.json')];assert len(sources)==1149
script=ast.parse((box/'check_c_abi.py').read_text())
node=next(n for n in script.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='pattern' for t in n.targets))
pattern=re.compile(ast.literal_eval(node.value.args[0]))
found={};total=0
for source in sources:
    bind(source,preflight['input_sha256'][str(source)])
    for match in pattern.finditer(source.read_text()):
        args=tuple(re.sub(r'\s+\w+$','',p.strip()) for p in match[3].split(',')) if match[3].strip() not in ['', 'void'] else ()
        found.setdefault(match[2],set()).add((match[1],args));total+=1
assert not {n for n,v in found.items() if len(v)>1}
assert total==preflight['declarations'] and len(found)==preflight['symbols']
bind(box/'c-abi-verification.json')
negative=load(box/'c-abi-negative-controls.json');assert negative['exit']==0;bind(box/'c-abi-negative-controls.json')
objects=shlex.split((box/'objects.rsp').read_text());assert len(objects)==1147
old_objects=shlex.split((shared/'objects.rsp').read_text())
assert objects==[state['replacements'].get(p,p) for p in old_objects]
assert len(state['replacements'])==3
main=shared/'generated/PublicDefaultActualNative.o';bind(main)
link=load(box/'native-link.json');assert link['exit']==0
expected=load(shared/'native-link.json')['command']
expected=['@'+str(box/'objects.rsp') if arg=='@'+str(shared/'objects.rsp') else arg for arg in expected]
exe=Path(state['executable']);expected[-1]=str(exe)
assert link['command']==expected and '-Wl,-undefined,error' in expected
bind(exe,state['executable_sha256']);bind(box/'native-link.json')
assert (box/'c-abi-verification.json').stat().st_mtime_ns < (box/'native-link.json').stat().st_mtime_ns
prefix=Path(config['binary']).parent.parent
providers=[Path(r['path']) for r in load(base/'native/official-package-providers.json')]
providers += [p for p in (prefix/'lib/lean').glob('*.dylib') if p.name in ['libleanshared.dylib','libLake_shared.dylib','libInit_shared.dylib'] or p.name.startswith('libleanshared_')]
def symbols(paths,flag):
    result=set()
    for start in range(0,len(paths),64):
        out=subprocess.check_output(['nm',flag,*map(str,paths[start:start+64])],text=True)
        result.update(p for p in out.splitlines() if p.startswith('_'))
    return result
definitions=symbols([Path(p) for p in objects]+[main]+providers,'-gUj')
required={s for s in symbols([exe],'-uj') if s.startswith(('_l_','_lp_','_initialize_','_runtime_initialize_','_meta_initialize_','_lean_'))}
assert not required-definitions,sorted(required-definitions)
links=subprocess.check_output(['otool','-L',str(exe)],text=True)
for row in load(base/'native/official-package-providers.json'):assert row['path'] in links
assert 'FlyCNS' not in links
init_path=box/'native-init-only.json'
if not init_path.exists():
    started=time.time()
    result=subprocess.run([str(exe),'--init-only'],cwd=root/'Lean',capture_output=True,text=True)
    init_path.write_text(json.dumps(dict(exit=result.returncode,seconds=round(time.time()-started,3),
        executable_sha256=sha(exe),output=result.stdout+result.stderr),indent=2)+'\n')
init=load(init_path)
assert init['exit']==0 and init['executable_sha256']==sha(exe) and 'consumer main not called' in init['output']
bind(init_path)
for p,wanted in inputs.items():assert sha(p)==wanted,p
record=dict(ready=True,executable=str(exe),executable_sha256=sha(exe),inputs=inputs,
    original_literal_source_sha256=old['original_literal_source_sha256'],init_only_passed=True,
    original_logical_modules_preserved=120,source_compiled_modules=121,
    reused_original_objects=old['reused_original_objects']-2,
    original_olean_reemitted_modules=old['original_olean_reemitted_modules'],official_package_libraries=8,
    abi_declarations=total,abi_symbols=len(found),abi_conflicts=0,
    lean_external_symbols=len(required),unresolved_lean_symbols=0,executed_main=False,goal_complete=False)
(box/'ready-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'DIRECT FINANCE READY PASS: frozen 119-owner base; three exact refreshes; 121 unique source owners; ABI declarations={total}; unresolved Lean symbols=0; initialization exit0')
