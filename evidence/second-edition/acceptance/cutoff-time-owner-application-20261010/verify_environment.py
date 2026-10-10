from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[3];BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
import first_release as fr
import source_view as sv
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,d:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')


def main():
 exported=json.loads((ROOT/'tools/export-map.json').read_bytes());inverse={r['target']:r for r in exported['modules']}
 row=next(r for r in exported['modules'] if r['path'].endswith('/SourceActualThreeParticleCutoffTime.lean'))
 imports=[m for _,_,m in sv.import_tokens((ROOT/row['path']).read_text()) if m.split('.')[0] not in sv.EXTERNAL]
 namespace='LowEnergy.'
 producers=[
  ('SourceFullYUncutRetardedKernel','FullYDynamicSourceNext',['oriented_causal_limit','causal_apply','time_negative']),
  ('SourceFullYPositiveOutputParseval','FourGradeOutputParseval',['baseline_time_square_integrable','baseline_frequency_square_integrable','baseline_square_mass','positive_output_parseval','square_pair_integrable','one_sided_positive_parseval']),
  ('SourceActualFourBlockSharpCausalMass','ActualFourBlockSharpCausalMass',['polynomial_wave_square_integrable'])]
 chosen={}
 for stem,ns,members in producers:
  available=[r for r in exported['modules'] if r['source_path'].endswith('/'+stem+'.lean')]
  if stem=='SourceActualFourBlockSharpCausalMass':provider=next(r for r in available if r['target'] in imports)
  else:
   assert len(available)==1;provider=available[0]
  chosen[stem]=provider
 rules=[{'source_expression':'(Name.str `_private "'+stem+'")','target_expression':'(`_private.'+chosen[stem]['target']+')','count':1} for stem,_,_ in producers]
 raw=(ROOT/row['path']).read_bytes();assert sha(ROOT/row['path'])==row['target_sha256'];assert row['source_sha256']=='6fa9a820792b2a8332be92dd4e5cf5704a6b335a760351e16079c559ebf7f71d'
 original=sv.module_views(row,inverse)
 candidate=sv.rewrite_private_owner_expressions(raw.decode(),rules).encode()
 assert sv.rewrite_private_owner_expressions(candidate.decode(),rules,reverse=True).encode()==raw
 out=fr.new_output(ROOT,BASE/'environment-verification-source72d341e7');src=out/'src';lib=out/'lib';src.mkdir();lib.mkdir()
 path=Path(row['target'].replace('.','/')).with_suffix('.lean');candidate_path=src/path;candidate_path.parent.mkdir(parents=True);candidate_path.write_bytes(candidate)
 reserved=path.with_suffix('.olean');ancestors=set(reserved.parents)
 def link_cache(public,private,relative=Path('.')):
  private.mkdir(exist_ok=True)
  for child in public.iterdir():
   rel=relative/child.name
   if rel.parent==reserved.parent and child.name.startswith(reserved.stem+'.'):continue
   dest=private/child.name
   if rel in ancestors:link_cache(child,dest,rel)
   else:dest.symlink_to(child,target_is_directory=child.is_dir())
 link_cache(ROOT/'Lean/.lake/build/lib/lean',lib)
 expected=[('LowEnergy.'+ns+'.'+member,chosen[stem]['target']) for stem,ns,members in producers for member in members]
 pairs='['+', '.join('('+json.dumps(name)+', '+json.dumps(owner)+')' for name,owner in expected)+']'
 probe=src/'OriginalCutoffPayers.lean'
 probe.write_text(''.join('import '+m+'\n' for m in imports)+'import Lean\nset_option autoImplicit false\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  for (text, owner) in '+pairs+' do\n    let wanted := text.toName\n    let candidates := env.constants.toList.filter fun (name,_) => privateToUserName name == wanted && name.toString.startsWith ("_private." ++ owner ++ ".")\n    unless candidates.length == 1 do throwError "Expected unique original payer {wanted} / {owner}"\n    let (name,info) := candidates[0]!\n    let some index := env.getModuleIdxFor? name | throwError "No module {name}"\n    unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong owner {name}"\n    unless (info.value? true).isSome do throwError "Missing checked value {name}"\n    logInfo m!"OWNER {wanted} = {name} MODULE {env.header.moduleNames[index]!}"\n    logInfo m!"TYPE {name} = {info.type}"\n')
 code=raw.decode();opening=code[code.index('set_option autoImplicit'):code.index('section PaidHelpers')]
 # The fixture reuses the source openings, with a distinct namespace for its local abbreviation/instance.
 opening=opening.replace('namespace LowEnergy.ActualThreeParticleCutoffTime','namespace CutoffIndependentConsumer')
 opening+='open LowEnergy.ActualThreeParticleCutoffTime\n'
 consumer=src/'IndependentCutoffTimeConsumer.lean';text='import '+row['target']+'\n'+opening
 for name,args in [('actual_wave_square_integrable','F n sharp advanced μ hμ x'),('actual_wave_fourier','F n sharp advanced μ hμ x ξ'),('actual_absolute_time_mass','F n sharp advanced μ hμ x')]:
  assert code.count('theorem '+name+' ')==1
  statement=code.split('theorem '+name,1)[1].split(' := by',1)[0]
  if ':=' in statement:statement=statement.split(' :=',1)[0]
  text+='example'+statement+' := '+name+' '+args+'\n\n'
 text+='end CutoffIndependentConsumer\n'
 for name in ('actual_wave_square_integrable','actual_wave_fourier','actual_absolute_time_mass'):text+='#print axioms LowEnergy.ActualThreeParticleCutoffTime.'+name+'\n'
 consumer.write_text(text)
 scope_path=ROOT/'.local/physics-acceptance-20261010/new9-charged-transfer-build-72d341e7-provenance/before.json';scope=json.loads(scope_path.read_bytes())['package_inputs']['v2-9c73-charged-transfer']
 paths=set(scope['files'])|{'Lean/lean-toolchain','Lean/lakefile.toml','Lean/lake-manifest.json',Path(__file__).relative_to(ROOT).as_posix(),scope_path.relative_to(ROOT).as_posix()}
 paths.update(p.relative_to(ROOT).as_posix() for p in (candidate_path,probe,consumer))
 def capture():return {'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'files':{p:sha(ROOT/p) for p in sorted(paths)}}
 before=capture();assert all(before['files'][p]==digest for p,digest in scope['files'].items());write(out/'input-before.json',before)
 (out/'invocation-source.py').write_bytes(Path(__file__).read_bytes())
 settings=fr.settings(ROOT);flags=list(dict.fromkeys(settings['package_moreLeanArgs']+settings['package_weakLeanArgs']+['--trust=0','-DwarningAsError=true']))
 env=fr.build_environment();assert env['LEAN_NUM_THREADS']=='2';original_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT/'Lean',text=True).strip();env['LEAN_PATH']=str(lib)+':'+original_path
 steps=[]
 def execute(name,source,object):
  command=['lean','--root='+str(src),*flags,str(source),'-o',str(object)];write(out/(name+'-command.json'),{'command':command,'cwd':'Lean','LEAN_NUM_THREADS':'2','LEAN_PATH':env['LEAN_PATH'],'settings':settings})
  start=time.monotonic();log=out/(name+'.log');object.parent.mkdir(parents=True,exist_ok=True)
  with log.open('x') as stream:
   process=subprocess.Popen(command,cwd=ROOT/'Lean',env=env,stdout=stream,stderr=subprocess.STDOUT);write(out/'handle.json',{'controller_pid':os.getpid(),'lean_pid':process.pid,'step':name});status=process.wait()
  result={'name':name,'exit_code':status,'elapsed_seconds':round(time.monotonic()-start,3),'command':command,'source_sha256':sha(source),'log_sha256':sha(log),'object_sha256':sha(object) if object.exists() else None};steps.append(result);write(out/'steps.json',steps);print(json.dumps(result),flush=True);return status==0
 ok=execute('actual-original-cutoff-payers',probe,out/'payers.olean')
 if ok:ok=execute('canonical-cutoff-time-candidate',candidate_path,lib/reserved)
 if ok:ok=execute('independent-cutoff-time-consumer',consumer,out/'consumer.olean')
 after=capture();write(out/'input-after.json',after);source_same=before['files']==after['files']
 result={'schema':'h0mework/private-cutoff-time-owner-verification@1','ok':ok and source_same,'inputs_unchanged':source_same,
         'identity_scope':'All actual3191 charged source bytes plus original project/compiler configuration and private driver/sources; global tooling/HEAD window is separately recorded.',
         'head_before':before['head'],'head_after':after['head'],'head_unchanged':before['head']==after['head'],
         'formal_acceptance':False,'public_path':row['path'],'original_source_sha256':row['source_sha256'],'candidate_public_sha256':sha(candidate_path),
         'candidate_inverse_public_bytes_exact':True,'private_owner_expression_rewrites':rules,
         'source_options':[line for line in code.splitlines() if line.startswith('set_option ')],
         'original_checked_payer_expectations':dict(expected),'producer_rows':chosen,'steps':steps,'source_scope_sha256':scope['digest']}
 write(out/'result.json',result);print(json.dumps({'ok':result['ok'],'inputs_unchanged':source_same,'steps':len(steps),'head_unchanged':result['head_unchanged']}),flush=True)
 return 0 if result['ok'] else 1

if __name__=='__main__':raise SystemExit(main())
