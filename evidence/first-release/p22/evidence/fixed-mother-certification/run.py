from pathlib import Path
import hashlib,json,os,subprocess,sys,time
r=Path.cwd(); c=r/'.cache/fixed-mother-certification'; p=r/'.cache/fixed-mother-theorem/capsule.json'
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(p)=='640fe14ce21eaffa176e614b0cf24d146a4ccb4f2dd2fe1d03b637b7dbe41fac'
a=json.loads(p.read_text()); parent=r/a['parent_production_manifest']; assert sha(parent)==a['parent_production_manifest_sha256']; m=json.loads(parent.read_text())
checks=[]
def verify():
 assert sha(parent)==a['parent_production_manifest_sha256']
 assert sha(Path(m['lean']))==m['lean_sha256']
 for i in a['files']: assert sha(r/i['file'])==i['sha256']
 for i in m['all_files']:
  assert sha(r/i['production'])==i['production_sha256'],i['production']
  assert sha(Path(i['production_olean']))==i['production_olean_sha256'],i['production_olean']
verify(); source=r/sys.argv[1]; phase=sys.argv[2] if len(sys.argv)>2 else 'candidate'
cache=c if phase=='candidate' else r/'.cache/fixed-mother-promotion'
out=cache/source.relative_to(r).with_suffix('.olean'); out.parent.mkdir(parents=True,exist_ok=True)
idx=1
while (cache/f'{source.stem}-{idx}.json').exists():idx+=1
log=cache/f'{source.stem}-{idx}.log'; receipt=cache/f'{source.stem}-{idx}.json'
env=os.environ.copy(); env['LEAN_PATH']=str(c)+':'+str(r/'.cache/fixed-mother-promotion')+':'+m['production_lean_path']
cmd=[m['lean'],'--trust=0','-DwarningAsError=true','-o',str(out),str(source)]; before=sha(source); started=time.monotonic()
with log.open('w') as stream: result=subprocess.run(cmd,env=env,stdout=stream,stderr=subprocess.STDOUT)
check={'source':str(source.relative_to(r)),'sha256':before,'source_unchanged':sha(source)==before,'command':cmd,'exit_code':result.returncode,'seconds':time.monotonic()-started,'log':str(log.relative_to(r))}
if result.returncode==0: check.update(olean=str(out),olean_sha256=sha(out))
verify(); check['parent_329_source_olean_unchanged']=True
receipt.write_text(json.dumps(check,indent=2)+'\n'); print(source.relative_to(r),'PASS' if not result.returncode else 'FAIL',f'{check["seconds"]:.1f}s',flush=True)
print(log.read_text()[-10000:],flush=True);sys.exit(result.returncode)
