from pathlib import Path
import os,subprocess,time,json,hashlib
repo=Path('runtime/Documents/Homework');state=Path(__file__).resolve().parent;parent=state/'input/lib';view=state/'focused/lib';view.mkdir(parents=True,exist_ok=True)
entries=[(e['module'],Path(e['source']),repo/'Lean') for e in json.loads((state/'formal-entries.json').read_text())[1:]]
def corridor(module):
 old=parent;new=view
 for name in module.split('.')[:-1]:
  if old.exists():
   for p in old.iterdir():
    if p.name==name:continue
    q=new/p.name
    if not q.exists() and not q.is_symlink():q.symlink_to(p.resolve(),target_is_directory=p.is_dir())
  q=new/name
  if q.is_symlink():q.unlink()
  q.mkdir(exist_ok=True);old=old/name;new=q
 if old.exists():
  for p in old.iterdir():
   q=new/p.name
   if not q.exists() and not q.is_symlink():q.symlink_to(p.resolve(),target_is_directory=p.is_dir())
for module,_,_ in entries:corridor(module)
default=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo/'Lean',text=True).strip();paths=[str(view),str(parent),default];env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');rows=json.loads((state/'focused.json').read_text())
for module,source,root in entries:
 output=view/(module.replace('.','/')+'.olean');assert not output.exists();cmd=['runtime/.elan/manual/lean-4.33.0-darwin_aarch64/bin/lean','--trust=0','-DElab.async=false','-DwarningAsError=true','-j1','-M16000','--root='+str(root),'-o',str(output),str(source)]
 before=hashlib.sha256(source.read_bytes()).hexdigest();start=time.monotonic();r=subprocess.run(cmd,cwd=repo/'Lean',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log=state/(module.rsplit('.',1)[1]+'.focused.log');log.write_text(r.stdout);row={'module':module,'source':str(source),'sha256_before':before,'sha256_after':hashlib.sha256(source.read_bytes()).hexdigest(),'output':str(output),'command':cmd,'LEAN_PATH':paths,'LEAN_NUM_THREADS':1,'exit':r.returncode,'seconds':time.monotonic()-start,'diagnostics':r.stdout,'log':str(log)}
 if r.returncode==0:row['olean_sha256']=hashlib.sha256(output.read_bytes()).hexdigest()
 rows.append(row);(state/'focused.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps({k:v for k,v in row.items() if k not in ('command','LEAN_PATH')},indent=2),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
