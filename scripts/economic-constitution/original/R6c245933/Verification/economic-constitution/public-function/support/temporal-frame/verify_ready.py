from pathlib import Path
import ast,hashlib,json,re,shlex,subprocess,time
root=Path('runtime/Documents/Homework');b=Path(__file__).absolute().parent;base=b.parent;prior=base/'root-frame'
load=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();inputs={}
def bind(p,wanted=None):
 p=Path(p);h=sha(p);assert wanted is None or h==wanted,str(p);inputs[str(p)]=h;return h
old=load(prior/'ready-verification.json');assert old['ready'] and old['init_only_passed'] and not old['executed_main']
for p,h in old['inputs'].items():bind(p,h)
bind(prior/'ready-verification.json')
certificate=load(b/'verification-check.json');assert certificate['certified'] and certificate['complete_function_equalities']==6
for p,h in certificate['inputs'].items():bind(p,h)
bind(b/'verification-check.json')
state=load(b/'status.json');rows=load(b/'hot-source-plan.json');assert state['exit']==0 and state['complete']==state['total']==len(rows)==6
plan=load(b/'source-plan.json');old_plan={r['module']:r for r in load(prior/'source-plan.json')};assert len(plan)==len({r['module'] for r in plan})==123
source_module='SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source'
assert {r['module'] for r in plan}==old_plan.keys()
old_sources=load(prior/'c-sources.json');selected={}
for p in old_sources:
 if 'Financed_Continuing_Runtime_stateAt' in Path(p).read_text() and not p.endswith('/Financed/Continuing/Runtime.c'):
  assert 'SaturationMonoid/' in p
  module='SaturationMonoid.'+p.split('SaturationMonoid/',1)[1][:-2].replace('/','.')
  selected[module]=p
assert selected=={r['module']:r['actual_c'] for r in rows}
config=load(b/'lean-env.json');inventory={r['module']:r for r in load(base/'native/module-inventory-checked.json')};old_objects=shlex.split((prior/'objects.rsp').read_text());expected={};edges=[]
paid={r['module']:load(b/(r['label']+'-compile.json')) for r in rows}
for i,row in enumerate(rows):
 r=paid[row['module']];assert r['exit']==0 and r['exact_dependencies'] and r['module']==row['module']
 assert r['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000)
 assert r['module_package']==row['package']==inventory[row['module']]['package'] is None and r['setup_sha256'] is None
 bind(b/(row['label']+'-compile.json'));bind(row['source'],r['source_sha256']);assert r['source_sha256']==row['source_sha256']
 assert Path(row['source'])==root/r['source']
 rel=Path(row['module'].replace('.','/')+'.olean');bind(b/'lib'/rel,r['artifact_sha256'])
 for module,h in r['dependencies'].items():
  rel=Path(module.replace('.','/')+'.olean');provider=next(Path(p)/rel for p in config['LEAN_PATH'].split(':') if (Path(p)/rel).exists());bind(provider,h)
  if module in paid:assert h==paid[module]['artifact_sha256']
  else:
   old_provider=next(Path(p)/rel for p in load(prior/'lean-env.json')['LEAN_PATH'].split(':') if (Path(p)/rel).exists())
   assert provider.resolve()==old_provider.resolve() and sha(old_provider)==h
  edges.append(dict(consumer=row['module'],provider=module,sha256=h))
 c=b/'generated'/Path(row['module'].replace('.','/')+'.c');assert r['c_path']==str(c);bind(c,r['c_sha256'])
 inv=inventory[row['module']];marker='LEAN_EXPORT lean_object* '+inv['initializer']+'(uint8_t builtin) {';code=c.read_text();assert code.count(marker)==1
 calls=re.findall(r'res = (initialize_\w+)\(builtin\)',code.split(marker,1)[1]);wanted=list(inv['import_initializers'])
 if inv['is_module']:wanted += [inv['runtime_initializer'],inv['comptime_initializer']]
 assert calls==wanted,row['module']
 obj=c.with_suffix('.o');record=load(b/('Object'+str(i)+'.json'));assert record['exit']==0 and record['c_sha256']==sha(c)
 assert record['command']==[str(Path(config['binary']).with_name('leanc')),'-c','-O2','-ffp-contract=off',str(c),'-o',str(obj)]
 bind(obj,record['object_sha256']);bind(b/('Object'+str(i)+'.json'))
 original=str(Path(row['actual_c']).with_suffix('.o'));assert original in old_objects;bind(row['actual_c'],row['actual_c_sha256']);expected[original]=str(obj)
assert state['replacements']==expected
objects=shlex.split((b/'objects.rsp').read_text());assert objects==[expected.get(p,p) for p in old_objects] and len(objects)==1147
sources=load(b/'c-sources.json');main=base/'shared-runtime/generated/PublicDefaultActualNative.c'
assert sources==[str(Path(p).with_suffix('.c')) for p in objects]+[str(main),str(base/'native/NativeBoot.c')]
preflight=load(b/'literal-preflight.json');assert preflight['accepted'] and preflight['exit']==0 and preflight['complete_module_c_byte_identical'] and not preflight['executed_main']
bind(b/'literal-preflight.json');bind(preflight['source'],preflight['source_sha256']);bind(preflight['artifact'],preflight['artifact_sha256']);bind(preflight['complete_c'],preflight['complete_c_sha256']);bind(preflight['reference_complete_c'],preflight['reference_complete_c_sha256'])
assert Path(preflight['complete_c']).read_bytes()==Path(preflight['reference_complete_c']).read_bytes()
bind(b/'preflight_literal.py',preflight['script_sha256'])
for p,h in preflight['imports'].items():bind(p,h)
binding=load(prior/'source-binding.json');assert binding['same_literal_consumer'] and not binding['executed_main']
bind(root/binding['source'],binding['source_sha256']);literal=next(r for r in plan if r['module']=='PublicDefaultActualNative')
assert literal['source_sha256']==binding['source_sha256']==old['original_literal_source_sha256'];assert Path(literal['source']).read_bytes()==(root/binding['source']).read_bytes()
bind(main,old['inputs'][str(main)]);bind(main.with_suffix('.o'),old['inputs'][str(main.with_suffix('.o'))])
identity=load(b/'identity-consumer-run.json');assert identity['exit']==0 and 'modules=6;' in identity['output'] and 'additiveDeclarations=12' in identity['output']
wanted_args=[]
for row in rows:
 rel=Path(row['module'].replace('.','/')+'.olean');wanted_args += [str(prior/'lib'/rel),str(b/'lib'/rel)]
assert identity['arguments']==wanted_args
for p in wanted_args:bind(p)
assert identity['source_sha256']==bind(b/'identity.lean')
for p,h in identity['imports'].items():bind(p,h)
ownership=load(b/'ownership-verification.json');assert ownership['accepted'] and ownership['modules']==6
for p,h in ownership['inputs'].items():bind(p,h)
abi=load(b/'c-abi-verification.json');assert abi['accepted'] and abi['executable_not_invoked']
tree=ast.parse((b/'check_c_abi.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='pattern' for t in n.targets));pattern=re.compile(ast.literal_eval(node.value.args[0]));found={};total=0
for p in sources:
 bind(p,abi['input_sha256'][p])
 for m in pattern.finditer(Path(p).read_text()):
  args=tuple(re.sub(r'\s+\w+$','',part.strip()) for part in m[3].split(',')) if m[3].strip() not in ['', 'void'] else ();found.setdefault(m[2],set()).add((m[1],args));total+=1
assert not {n:s for n,s in found.items() if len(s)>1};assert total==abi['declarations'] and len(found)==abi['symbols'];assert load(b/'c-abi-negative-controls.json')['exit']==0
link=load(b/'native-link.json');proof=load(b/'link-verification.json');assert link['exit']==0 and proof['linked'] and not proof['missing_live_providers']
exe=Path(proof['executable']);cmd=['@'+str(b/'objects.rsp') if a=='@'+str(prior/'objects.rsp') else a for a in load(prior/'native-link.json')['command']];cmd[-1]=str(exe)
assert link['command']==cmd and '-Wl,-undefined,error' in cmd and proof['exact_replacements']==expected;bind(exe,proof['executable_sha256'])
linked=subprocess.check_output(['otool','-L',str(exe)],text=True)
for provider in load(base/'native/official-package-providers.json'):bind(provider['path'],provider['sha256']);assert provider['path'] in linked
assert 'FlyCNS' not in linked
for name in ['lean-env.json','source-plan.json','hot-source-plan.json','objects.rsp','c-sources.json','verify_ready.py','check_c_abi.py','c-abi-verification.json','c-abi-negative-controls.json','identity-consumer-run.json','ownership-verification.json','native-link.json','link-verification.json','compile_overlay.py']:
 bind(b/name)
init_path=b/'native-init-only.json'
if not init_path.exists():
 print('TEMPORAL FRAME PRE-INIT CHECK PASS: exact 6-owner replacement map, literal source/C/object, original packages, IR borrowing and live symbols verified; entering initialization only',flush=True)
 began=time.time();r=subprocess.run([str(exe),'--init-only'],cwd=root/'Lean',capture_output=True,text=True)
 init_path.write_text(json.dumps(dict(exit=r.returncode,seconds=round(time.time()-began,3),executable_sha256=sha(exe),output=r.stdout+r.stderr),indent=2)+'\n')
init=load(init_path);assert init['exit']==0 and init['executable_sha256']==sha(exe) and 'consumer main not called' in init['output'];bind(init_path)
for name in ['source-binding.json','extra-exports-plan.json']:(b/name).write_bytes((prior/name).read_bytes());bind(b/name,sha(prior/name))
for p,h in inputs.items():assert sha(p)==h,p
record=dict(ready=True,executable=str(exe),executable_sha256=sha(exe),inputs=inputs,original_literal_source_sha256=binding['source_sha256'],init_only_passed=True,original_logical_modules_preserved=122,source_compiled_modules=123,reused_original_objects=old['reused_original_objects'],original_olean_reemitted_modules=old['original_olean_reemitted_modules'],official_package_libraries=8,abi_declarations=total,abi_symbols=len(found),abi_conflicts=0,lean_external_symbols=proof['live_lean_external_symbols'],unresolved_lean_symbols=0,dependency_edges=edges,changed_ownership_signatures=ownership['changed_ownership_signatures'],removed_ir_helpers=ownership['removed_ir_helpers'],executed_main=False,goal_complete=False)
(b/'ready-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'TEMPORAL FRAME READY PASS: 6 exact owners / 123 source union; original complete visit and process consumer; ABI={total}/{len(found)}; ownership, live symbols, same literal and initialization exit0')
