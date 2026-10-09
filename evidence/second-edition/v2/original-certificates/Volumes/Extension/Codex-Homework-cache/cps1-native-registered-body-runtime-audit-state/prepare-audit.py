from pathlib import Path
import hashlib,json,re,shutil,sys
repo=Path('runtime/Documents/Homework');state=Path(__file__).resolve().parent
prior=repo/'ComputeNode/state/cps1-native-root-installation-audit'
bootstrap=json.loads((state/'bootstrap.json').read_text());promotion=json.loads(Path(sys.argv[1]).read_text())
parent=Path(bootstrap['parent_receipt']['path']);assert hashlib.sha256(parent.read_bytes()).hexdigest()==bootstrap['parent_receipt']['sha256']
src=state/'input/src';entries=promotion['entries'];modules=[];sources={};files=[];mouths=[]
B='SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.'
for row in entries:
 source=Path(row['source']);assert hashlib.sha256(source.read_bytes()).hexdigest()==row['sha256'],str(source)
 module=row['module'];rel=module.replace('.','/')+'.lean';target=src/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
 modules.append(module);sources[str(source.relative_to(repo))]=row['sha256'];files.append('src/'+rel)
 for hit in re.finditer(r'^(?:noncomputable )?(def|abbrev|theorem|structure|inductive) ([A-Za-z_][A-Za-z0-9_?.]*)',source.read_text(),re.M):mouths.append(B+hit[2])
assert len(mouths)==len(set(mouths));required=promotion.get('required_value_paths',{})
assert set(required)<=set(mouths),set(required)-set(mouths)
checks=[[name,required.get(name,[])] for name in mouths]
contract={'schema':'CPS1-native-registered-body-runtime-audit-contract/v1','modules':modules,'sources':sources,'mouths':mouths,'checks':checks,'data_mouths':[B+'registered_body_runtime'],'capture_data_mouths':[],'capture_entry_points':[],'live_mouths':list(required),'forbidden_live_prefixes':['CPS1BiologicalUpdate.SourcePositive.'],'forbidden_live_names':[],'scope':promotion['scope'],'source_review':promotion['source_review']}
(state/'audit-contract.json').write_text(json.dumps(contract,indent=2)+'\n')
tool=(prior/'input/src/NativeRootInstallationAuditTools.lean').read_text()
tool=re.sub(r'private def ownerModules : List Name := .*','private def ownerModules : List Name := ['+','.join('`'+m for m in modules)+']',tool,count=1)
tool=tool.replace('auditNativeRootInstallationCandidate','auditNativeRegisteredBodyRuntimeCandidate')
i=tool.index('  let checks : Array (Name × Array Name) := #[');j=tool.index('\n  let mut valueRows',i)
tool=tool[:i]+'  let checks : Array (Name × Array Name) := #[\n'+',\n'.join('    (`'+n+', #['+','.join('`'+d for d in ds)+'])' for n,ds in checks)+'\n  ]'+tool[j:]
tool=re.sub(r'  for mouth in #\[.*?\] do','  for mouth in #['+','.join('`'+m for m in mouths)+'] do',tool,count=1)
(src/'NativeRegisteredBodyRuntimeAuditTools.lean').write_text(tool)
imports=''.join('import '+m+'\n' for m in modules)
(src/'ExecuteAudit.lean').write_text(imports+'import NativeRegisteredBodyRuntimeAuditTools\nauditNativeRegisteredBodyRuntimeCandidate\n')
(src/'Axioms.lean').write_text(imports+''.join('#print axioms '+m+'\n' for m in mouths))
math_files=list(files);files+=['src/paid-names-native-registered-body-runtime.txt','src/NativeRegisteredBodyRuntimeAuditTools.lean','src/ExecuteAudit.lean','src/Axioms.lean']
profile=hashlib.sha256(parent.read_bytes()+''.join(bootstrap['shared']).encode()+b''.join((state/'input'/p).read_bytes() for p in math_files)).hexdigest()
old=json.loads((prior/'units.jsonl').read_text().splitlines()[-1]);runner=old['argv'][2];runner=runner[:runner.index('\ncompile_gate "')]
runner=runner.replace(json.loads((prior/'preparation.json').read_text())['proof_gate_profile'],profile).replace('paid-names-native-root-installation','paid-names-native-registered-body-runtime')
runner+='\n'+''.join('compile_gate "'+m.replace('.','/')+'" "'+m.replace('.','/')+'.lean"\n' for m in modules)
for m in ['NativeRegisteredBodyRuntimeAuditTools','ExecuteAudit']:runner+='lean --trust=0 -DElab.async=false -DwarningAsError=true -M32000 -j1 -o "$PCNODE_OUT/'+m+'.olean" "$PCNODE_SRC/src/'+m+'.lean"\n'
runner+='lean --trust=0 -DElab.async=false -DwarningAsError=true -M32000 -j1 "$PCNODE_SRC/src/Axioms.lean" > "$PCNODE_OUT/axioms.log" 2>&1\n'
unit={**old,'argv':['bash','-lc',runner],'files':files,'shared':bootstrap['shared'],'outputs':[m.replace('.','/')+'.olean' for m in modules]+['NativeRegisteredBodyRuntimeAuditTools.olean','axioms.log']+[p for p in old['outputs'] if p.startswith('ExecuteAudit.') or p=='math-gates.log']}
unit['id']='native-registered-body-runtime-execute-audit@'+hashlib.sha256(profile.encode()+runner.encode()+b''.join((state/'input'/p).read_bytes() for p in files)).hexdigest()[:16]
(state/'units.jsonl').write_text(json.dumps(unit,separators=(',',':'))+'\n');destination=state/'results'/unit['id'];assert not destination.exists();destination.symlink_to(bootstrap['canonical_outputs'],target_is_directory=True)
report={'id':unit['id'],'proof_gate_profile':profile,'sources':sources,'math_gates':len(modules),'mouths':len(mouths),'value_paths':len(checks),'shared_count':len(bootstrap['shared']),'parent_receipt_sha256':bootstrap['parent_receipt']['sha256']}
(state/'preparation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='sources'},indent=2))
