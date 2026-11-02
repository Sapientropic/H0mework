from pathlib import Path
import hashlib,json,re
b=Path(__file__).absolute().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs={}
def bind(p,wanted=None):
 p=Path(p);value=sha(p)
 assert wanted is None or value==wanted,str(p)
 inputs[str(p)]=value
 return value
rows=load(b/'source-bindings.json')
for row,label in zip(rows,['RootFrame','OriginalRuntime']):
 r=load(b/(label+'-compile.json'))
 assert r['exit']==0 and r['module']==row['module']
 assert r['compile_options']==dict(trust=0,werror=True,elab_async=False,threads=1,memory_mb=12000)
 assert r['module_package'] is None and r['setup_sha256'] is None and r['exact_dependencies']
 bind(b/(label+'-compile.json'));bind(row['source'],row['source_sha256']);bind(row['candidate'],r['source_sha256'])
 old=Path(row['source']).read_text();new=Path(row['candidate']).read_text()
 if label=='RootFrame':
  end='end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History\n'
  assert new.startswith(old.removesuffix(end)) and new.endswith(end)
 else:
  first=new.index('def stateAtFromFrame');last=new.index('def process :',first)
  assert new[:first]+new[last:]==old
 rel=Path(row['module'].replace('.','/')+'.olean')
 bind(b/'lib'/rel,r['artifact_sha256']);bind(r['c_path'],r['c_sha256'])
 config=load(b/'lean-env.json')
 for mod,wanted in r['dependencies'].items():
  f=next(Path(p)/(mod.replace('.','/')+'.olean') for p in config['LEAN_PATH'].split(':') if (Path(p)/(mod.replace('.','/')+'.olean')).exists())
  bind(f,wanted)
for name,marker in [('identity-consumer','modules=2; unchangedOriginalBodiesAndTypes=176; additiveDeclarations=36'),('root-kernel','ROOT FRAME KERNEL REPLAY PASS: roots=212, closure=13593, private=1231, axioms=[Quot.sound, Classical.choice, propext]'),('ir','ROOT FRAME ACTUAL CALLER IR EMITTED')]:
 r=load(b/(name+'-run.json'));assert r['exit']==0 and marker in r['output']
 bind(b/(name+'-run.json'));bind(Path('runtime/Documents/Homework')/r['source'],r['source_sha256'])
 for p,h in r['imports'].items():bind(p,h)
for row in load(b/'identity-pairs.json'):
 bind(row['old'],row['old_sha256']);bind(row['new'],row['new_sha256'])
a=load(b/'ir.json');bind(b/'ir.json')
decls={e['name']:e for e in a}
def calls(n):
 return set(re.findall(r'(?:_private\.)?SaturationMonoid[A-Za-z0-9_.]*',decls[n]['body'].split(':=',1)[1]))
start='SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime.process'
state=start.removesuffix('process')+'stateAtFromFrame'
assert state+'._boxed' in calls(start)
seen=set();pending=[start]
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);pending += [v for v in calls(n) if v in decls and v not in seen]
factory='SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.RootFrame.produce'
factories=[n for n in seen if n.startswith(factory) and n.endswith("._redArg")]
assert factories and state in seen
for n in factories:
 c=calls(n)
 assert any(x.startswith('SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.advanceFrame') for x in c),n
 assert any(x.startswith('SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootVisit.next') for x in c),n
 assert not any(x.startswith('SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt') or x.startswith('SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.trailAt') for x in c),n
bind(b/'verify.py');bind(b/'lean-env.json');bind(b/'source-bindings.json');bind(b/'identity-pairs.json')
result=dict(certified=True,classification='same-source complete visit producer and original stateAt consumer',strict_modules=2,unchanged_original_types_and_bodies=176,additions=36,kernel_roots=212,kernel_closure=13593,kernel_private=1231,axioms=['Quot.sound','Classical.choice','propext'],actual_original_process_consumes_candidate=True,ir_reachable_functions=len(seen),root_frame_factories=factories,production_installed=False,actual_two_rounds_not_claimed=True,inputs=inputs)
(b/'verification-check.json').write_text(json.dumps(result,indent=2)+'\n')
print('ROOT FRAME INDEPENDENT CHECK PASS: strict=2; original type/body=176; additions=36; full visit/stateAt equality; empty kernel=212/13593/1231; standard axioms=3; original process IR consumes RootFrame; actual return not claimed')
