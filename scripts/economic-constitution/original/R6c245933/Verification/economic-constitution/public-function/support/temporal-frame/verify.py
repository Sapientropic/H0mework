from pathlib import Path
import hashlib,json,re
b=Path(__file__).absolute().parent;root=Path('runtime/Documents/Homework');load=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();inputs={}
def bind(p,h=None):
 p=Path(p);value=sha(p);assert h is None or value==h,str(p);inputs[str(p)]=value;return value
rows=load(b/'source-bindings.json');config=load(b/'lean-env.json');assert len(rows)==6
for row in rows:
 r=load(b/(row['label']+'-compile.json'));assert r['exit']==0 and r['module']==row['module'] and r['exact_dependencies']
 assert r['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000) and r['module_package'] is None and r['setup_sha256'] is None
 bind(row['source'],row['source_sha256']);assert r['source_sha256']==row['source_sha256'];bind(row['original_source'],row['original_source_sha256']);bind(b/(row['label']+'-compile.json'))
 old=Path(row['original_source']).read_text();new=Path(row['source']).read_text();a=new.index('def stateAtFromFrame');z=new.index('def process',a)
 assert new[:a]+new[z:]==old and 'stateAtFromFrame' not in old
 rel=Path(row['module'].replace('.','/')+'.olean');bind(b/'lib'/rel,r['artifact_sha256']);bind(r['c_path'],r['c_sha256'])
 for module,h in r['dependencies'].items():
  rel=Path(module.replace('.','/')+'.olean');provider=next(Path(p)/rel for p in config['LEAN_PATH'].split(':') if (Path(p)/rel).exists());bind(provider,h)
for name,marker in [('identity-consumer','modules=6; unchangedOriginalBodiesAndTypes=359; additiveDeclarations=12'),('temporal-kernel','TEMPORAL FRAME KERNEL REPLAY PASS: roots=12, closure=15814, private=1388, axioms=[Quot.sound, Classical.choice, propext]'),('ir','TEMPORAL FRAME SIX ACTUAL CALLERS IR EMITTED')]:
 r=load(b/(name+'-run.json'));assert r['exit']==0 and marker in r['output'];bind(b/(name+'-run.json'));bind(root/r['source'],r['source_sha256'])
 for p,h in r['imports'].items():bind(p,h)
for r in load(b/'identity-pairs.json'):bind(r['old'],r['old_sha256']);bind(r['new'],r['new_sha256'])
ir=load(b/'ir.json');bind(b/'ir.json');d={e['name']:e for e in ir}
def calls(n):return set(re.findall(r'(?:_private\.)?SaturationMonoid[A-Za-z0-9_.]*',d[n]['body'].split(':=',1)[1]))
factory='SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.RootFrame.produce'
chains=[]
for row in rows:
 process=row['namespace']+'.process';frame=row['namespace']+'.stateAtFromFrame'
 assert frame+'._boxed' in calls(process),(process,calls(process))
 assert any(x.startswith('SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.foldedRootVisitAt') for x in calls(frame))
 seen=set();pending=[frame]
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n);pending += [x for x in calls(n) if x in d and x not in seen]
 factories=sorted(n for n in seen if n.startswith(factory) and n.endswith('._redArg'));assert factories,row['module']
 for n in factories:
  c=calls(n)
  assert any(x.startswith('SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.advanceFrame') for x in c)
  assert any(x.startswith('SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootVisit.next') for x in c)
  assert not any(x.startswith('SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt') or x.startswith('SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.trailAt') for x in c)
 chains.append(dict(module=row['module'],process=process,frame=frame,factories=factories))
for p in ['verify.py','lean-env.json','source-bindings.json','identity-pairs.json']:bind(b/p)
result=dict(certified=True,strict_modules=6,unchanged_original_types_and_bodies=359,additions=12,complete_function_equalities=6,kernel_roots=12,kernel_closure=15814,kernel_private=1388,axioms=['Quot.sound','Classical.choice','propext'],actual_process_ir_consumers=chains,actual_two_rounds_not_claimed=True,production_installed=False,inputs=inputs)
(b/'verification-check.json').write_text(json.dumps(result,indent=2)+'\n')
print('TEMPORAL FRAME INDEPENDENT CHECK PASS: strict=6; original type/body=359; equalities=6; empty kernel=12/15814/1388; standard axioms=3; all six original process IRs consume the complete frame factory')
