from pathlib import Path
import os,subprocess,time,json,hashlib
repo=Path('runtime/Documents/Homework'); state=Path(__file__).resolve().parent
module='SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.RegisteredBody'
source=repo/'Lean'/(module.replace('.','/')+'.lean');output=state/'focused/lib'/(module.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
default=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo/'Lean',text=True).strip()
paths=[str(state/'input/lib'),default]; env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1')
cmd=['runtime/.elan/manual/lean-4.33.0-darwin_aarch64/bin/lean','--trust=0','-DElab.async=false','-DwarningAsError=true','-j1','-M16000','--root='+str(repo/'Lean'),'-o',str(output),str(source)]
before=hashlib.sha256(source.read_bytes()).hexdigest();start=time.monotonic();r=subprocess.run(cmd,cwd=repo/'Lean',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(state/'focused.log').write_text(r.stdout);row={'source':str(source),'sha256_before':before,'sha256_after':hashlib.sha256(source.read_bytes()).hexdigest(),'output':str(output),'command':cmd,'LEAN_PATH':paths,'LEAN_NUM_THREADS':1,'exit':r.returncode,'seconds':time.monotonic()-start,'diagnostics':r.stdout}
if r.returncode==0:row['olean_sha256']=hashlib.sha256(output.read_bytes()).hexdigest()
(state/'focused.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:v for k,v in row.items() if k not in ('LEAN_PATH','command')},indent=2),flush=True);raise SystemExit(r.returncode)
