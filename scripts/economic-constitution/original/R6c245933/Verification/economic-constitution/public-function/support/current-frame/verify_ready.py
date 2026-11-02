from pathlib import Path
import ast,hashlib,json,re,shlex,subprocess,time
root=Path('runtime/Documents/Homework');b=Path(__file__).absolute().parent;base=b.parent;prior=base/'temporal-frame'
load=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();inputs={}
def bind(path,wanted=None):
 path=Path(path);digest=sha(path);assert wanted is None or digest==wanted,str(path);inputs[str(path)]=digest;return digest
old=load(prior/'ready-verification.json');assert old['ready'] and old['init_only_passed'] and not old['executed_main']
for path,digest in old['inputs'].items():bind(path,digest)
bind(prior/'ready-verification.json')
certificate=load(b/'verification-check.json');assert certificate['certified'] and certificate['complete_function_equality'] and certificate['original_core_artifact_unchanged']
for path,digest in certificate['inputs'].items():bind(path,digest)
bind(b/'verification-check.json')
state=load(b/'native-status.json');rows=load(b/'selected-refresh-plan.json');assert state['exit']==0 and state['complete']==state['total']==len(rows)==30
plan=load(b/'source-plan.json');by={r['module']:r for r in plan};oldplan={r['module']:r for r in load(prior/'source-plan.json')};assert len(by)==len(plan)==125
assert by.keys()==oldplan.keys()|{r['module'] for r in rows}
newmodule='SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.CurrentFrame'
assert {r['module'] for r in rows if r['actual_c'] is None}=={newmodule}
config=load(b/'lean-env.json');inventory={r['module']:r for r in load(base/'native/module-inventory-checked.json')};oldobjects=shlex.split((prior/'objects.rsp').read_text());expected={};added=[];edges=[]
paid={r['module']:load(b/(r['label']+'-compile.json')) for r in rows}
newinit='initialize_'+newmodule.replace('.','_')
for index,row in enumerate(rows):
 rec=paid[row['module']];assert rec['exit']==0 and rec['exact_dependencies'] and rec['module']==row['module']
 assert rec['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000)
 assert rec['module_package']==row['package']
 if row['actual_c'] is not None:assert row['package']==inventory[row['module']]['package']
 else:assert row['module']==newmodule and row['package'] is None
 setup=config.get('module_setups',{}).get(row['module'])
 if setup:assert bind(setup,rec['setup_sha256']) and load(setup)['package']==row['package']
 else:assert rec['setup_sha256'] is None
 bind(b/(row['label']+'-compile.json'));bind(row['source'],row['source_sha256']);assert rec['source_sha256']==row['source_sha256']
 assert Path(row['source'])==root/rec['source']
 rel=Path(row['module'].replace('.','/')+'.olean');bind(b/'lib'/rel,rec['artifact_sha256'])
 for module,digest in rec['dependencies'].items():
  rel=Path(module.replace('.','/')+'.olean');provider=next(Path(d)/rel for d in config['LEAN_PATH'].split(':') if (Path(d)/rel).exists());bind(provider,digest)
  if module in paid:assert digest==paid[module]['artifact_sha256']
  else:
   original=next(Path(d)/rel for d in load(prior/'lean-env.json')['LEAN_PATH'].split(':') if (Path(d)/rel).exists());assert provider.resolve()==original.resolve() and sha(original)==digest
  edges.append(dict(consumer=row['module'],provider=module,sha256=digest))
 code=b/'generated'/Path(row['module'].replace('.','/')+'.c');assert rec['c_path']==str(code);bind(code,rec['c_sha256'])
 if row['module']==newmodule:
  initializer=newinit;wanted=['initialize_Init','initialize_Init',inventory['SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingExecution']['initializer']]
 else:
  inv=inventory[row['module']];initializer=inv['initializer'];wanted=list(inv['import_initializers'])
  if row['module'].endswith('Mandate.Financed.Repair.Source'):wanted.insert(2,newinit)
  if inv['is_module']:wanted += [inv['runtime_initializer'],inv['comptime_initializer']]
 marker='LEAN_EXPORT lean_object* '+initializer+'(uint8_t builtin) {';text=code.read_text();assert text.count(marker)==1
 calls=re.findall(r'res = (initialize_\w+)\(builtin\)',text.split(marker,1)[1]);assert calls==wanted,(row['module'],calls,wanted)
 obj=code.with_suffix('.o');record=load(b/('Object'+str(index)+'.json'));assert record['exit']==0 and record['c_sha256']==sha(code)
 assert record['command']==[str(Path(config['binary']).with_name('leanc')),'-c','-O2','-ffp-contract=off',str(code),'-o',str(obj)]
 bind(obj,record['object_sha256']);bind(b/('Object'+str(index)+'.json'))
 if row['actual_c'] is None:added.append(str(obj))
 else:
  original=str(Path(row['actual_c']).with_suffix('.o'));assert original in oldobjects;bind(row['actual_c'],old['inputs'][row['actual_c']]);expected[original]=str(obj)
 assert by[row['module']]['source_sha256']==row['source_sha256']
assert state['replacements']==expected and state['added_objects']==added
objects=shlex.split((b/'objects.rsp').read_text());assert objects==[expected.get(p,p) for p in oldobjects]+added and len(objects)==1148
sources=load(b/'c-sources.json');main=base/'shared-runtime/generated/PublicDefaultActualNative.c';assert sources==[str(Path(p).with_suffix('.c')) for p in objects]+[str(main),str(base/'native/NativeBoot.c')]
preflight=load(b/'literal-preflight.json');assert preflight['accepted'] and preflight['exit']==0 and preflight['complete_module_c_byte_identical'] and not preflight['executed_main']
bind(b/'literal-preflight.json')
for pathkey,hashkey in [('source','source_sha256'),('artifact','artifact_sha256'),('complete_c','complete_c_sha256'),('reference_complete_c','reference_complete_c_sha256')]:bind(preflight[pathkey],preflight[hashkey])
assert Path(preflight['complete_c']).read_bytes()==Path(preflight['reference_complete_c']).read_bytes();bind(b/'preflight_literal.py',preflight['script_sha256'])
for path,digest in preflight['imports'].items():bind(path,digest)
binding=load(prior/'source-binding.json');assert binding['same_literal_consumer'] and not binding['executed_main'];bind(root/binding['source'],binding['source_sha256'])
literal=by['PublicDefaultActualNative'];assert literal['source_sha256']==binding['source_sha256']==old['original_literal_source_sha256'];assert Path(literal['source']).read_bytes()==(root/binding['source']).read_bytes()
bind(main,old['inputs'][str(main)]);bind(main.with_suffix('.o'),old['inputs'][str(main.with_suffix('.o'))])
identity=load(b/'native-identity-consumer-run.json');assert identity['exit']==0 and 'modules=29;' in identity['output'] and 'unchangedOriginalBodiesAndTypes=2069; additiveDeclarations=0' in identity['output']
wantedargs=[]
for row in rows:
 if row['actual_c'] is not None:
  rel=Path(row['module'].replace('.','/')+'.olean');wantedargs += [str(prior/'lib'/rel),str(b/'lib'/rel)]
assert identity['arguments']==wantedargs
for path in wantedargs:bind(path)
assert identity['source_sha256']==bind(b/'identity.lean')
for path,digest in identity['imports'].items():bind(path,digest)
ownership=load(b/'ownership-verification.json');assert ownership['accepted'] and ownership['modules']==29 and not ownership['changed_ownership_signatures']
for path,digest in ownership['inputs'].items():bind(path,digest)
# Replay the source-bound C declarations rather than consuming the producer PASS flag.
abi=load(b/'c-abi-verification.json');assert abi['accepted'] and abi['executable_not_invoked']
tree=ast.parse((b/'check_c_abi.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='pattern' for t in n.targets));pattern=re.compile(ast.literal_eval(node.value.args[0]));found={};total=0
for path in sources:
 bind(path,abi['input_sha256'][path])
 for match in pattern.finditer(Path(path).read_text()):
  args=tuple(re.sub(r'\s+\w+$','',part.strip()) for part in match[3].split(',')) if match[3].strip() not in ['', 'void'] else ();found.setdefault(match[2],set()).add((match[1],args));total+=1
assert not {n:v for n,v in found.items() if len(v)>1};assert total==abi['declarations'] and len(found)==abi['symbols'];assert load(b/'c-abi-negative-controls.json')['exit']==0
link=load(b/'native-link.json');proof=load(b/'link-verification.json');assert link['exit']==0 and proof['linked'] and not proof['missing_live_providers']
exe=Path(proof['executable']);cmd=['@'+str(b/'objects.rsp') if arg=='@'+str(prior/'objects.rsp') else arg for arg in load(prior/'native-link.json')['command']];cmd[-1]=str(exe)
assert link['command']==cmd and '-Wl,-undefined,error' in cmd and proof['exact_replacements']==expected and proof['added_objects']==added;bind(exe,proof['executable_sha256'])
linked=subprocess.check_output(['otool','-L',str(exe)],text=True);providers=[Path(r['path']) for r in load(base/'native/official-package-providers.json')]
for provider in load(base/'native/official-package-providers.json'):bind(provider['path'],provider['sha256']);assert provider['path'] in linked
assert 'FlyCNS' not in linked
prefix=Path(config['binary']).parent.parent;providers += [p for p in (prefix/'lib/lean').glob('*.dylib') if p.name in ['libleanshared.dylib','libLake_shared.dylib','libInit_shared.dylib'] or p.name.startswith('libleanshared_')]
def symbols(paths,flag):
 result=set()
 for offset in range(0,len(paths),64):result.update(line for line in subprocess.check_output(['nm',flag,*map(str,paths[offset:offset+64])],text=True).splitlines() if line.startswith('_'))
 return result
needed={s for s in symbols([exe],'-uj') if s.startswith(('_l_','_lp_','_initialize_','_runtime_initialize_','_meta_initialize_','_lean_'))};definitions=symbols([Path(p) for p in objects]+[main.with_suffix('.o')]+providers,'-gUj');assert not needed-definitions;assert len(needed)==proof['live_lean_external_symbols']
for name in ['lean-env.json','source-plan.json','selected-refresh-plan.json','ownership-source-plan.json','objects.rsp','c-sources.json','verify_ready.py','check_c_abi.py','c-abi-verification.json','c-abi-negative-controls.json','native-identity-consumer-run.json','ownership-verification.json','native-link.json','link-verification.json','compile_overlay.py']:bind(b/name)
initpath=b/'native-init-only.json'
if not initpath.exists():
 print('CURRENT FRAME PRE-INIT INDEPENDENT PASS: 29 exact replacements + new module, 2069 original types/bodies, full C ABI, IR ownership, original packages/initializers and live symbols; entering original initialization only',flush=True)
 began=time.time();run=subprocess.run([str(exe),'--init-only'],cwd=root/'Lean',capture_output=True,text=True);initpath.write_text(json.dumps(dict(exit=run.returncode,seconds=round(time.time()-began,3),executable_sha256=sha(exe),output=run.stdout+run.stderr),indent=2)+'\n')
init=load(initpath);assert init['exit']==0 and init['executable_sha256']==sha(exe) and 'consumer main not called' in init['output'];bind(initpath)
for name in ['source-binding.json','extra-exports-plan.json']:(b/name).write_bytes((prior/name).read_bytes());bind(b/name,sha(prior/name))
for path,digest in inputs.items():assert sha(path)==digest,path
originals=load(base/'native/original-project-inputs.json');extra=load(b/'extra-exports-plan.json');reused=len(originals)-len({r['module'] for r in originals}&by.keys())-len(extra)
record=dict(ready=True,executable=str(exe),executable_sha256=sha(exe),inputs=inputs,original_literal_source_sha256=binding['source_sha256'],init_only_passed=True,original_logical_modules_preserved=123,standalone_proved_readout_modules=1,source_compiled_modules=125,reused_original_objects=reused,original_olean_reemitted_modules=len(extra),official_package_libraries=8,abi_declarations=total,abi_symbols=len(found),abi_conflicts=0,lean_external_symbols=len(needed),unresolved_lean_symbols=0,dependency_edges=edges,changed_ownership_signatures=ownership['changed_ownership_signatures'],removed_ir_helpers=ownership['removed_ir_helpers'],executed_main=False,goal_complete=False)
(b/'ready-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('CURRENT FRAME READY PASS: 30 exact owners / 125 source union; 2069 original declarations unchanged; complete function equality; original full literal C; ABI, borrowing, original libraries, live symbols and initialization exit0')
