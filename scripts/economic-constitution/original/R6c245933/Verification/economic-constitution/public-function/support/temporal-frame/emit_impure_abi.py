from pathlib import Path
import hashlib,json,os,subprocess,sys,time
box=Path(__file__).absolute().parent
which=sys.argv[1]
config_path=box/'lean-env.json' if which=='new' else box.parent/'root-frame/lean-env.json'
c=json.loads(config_path.read_text());source=box/'impure-abi.lean';target=box/(which+'-impure-abi.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
imports={}
for row in json.loads((box/'hot-source-plan.json').read_text()):
 relative=Path(row['module'].replace('.','/')+'.olean')
 artifact=next(Path(p)/relative for p in c['LEAN_PATH'].split(':') if (Path(p)/relative).exists())
 imports[str(artifact)]=sha(artifact)
started=time.time()
r=subprocess.run([c['binary'],'--trust=0','-DwarningAsError=true','-DElab.async=false','-j1','-M12000',str(source)],cwd='Lean',env=dict(os.environ,LEAN_PATH=c['LEAN_PATH'],HW_IR_ABI=str(target)),capture_output=True,text=True)
assert all(sha(p)==wanted for p,wanted in imports.items())
record=dict(exit=r.returncode,seconds=round(time.time()-started,3),source_sha256=sha(source),config_sha256=sha(config_path),imports=imports,output_sha256=sha(target) if r.returncode==0 else None,output=r.stdout+r.stderr)
(box/(which+'-impure-abi-run.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2));raise SystemExit(r.returncode)
