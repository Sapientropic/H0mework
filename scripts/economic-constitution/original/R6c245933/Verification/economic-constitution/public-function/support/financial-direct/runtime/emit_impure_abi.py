from pathlib import Path
import hashlib,json,os,subprocess,sys,time
box=Path(__file__).absolute().parent
which=sys.argv[1]
config_path=box/'lean-env.json' if which=='new' else box.parents[1]/'shared-runtime/lean-env.json'
c=json.loads(config_path.read_text());source=box/'impure-abi.lean';target=box/(which+'-impure-abi.json')
started=time.time()
r=subprocess.run([c['binary'],'--trust=0','-DwarningAsError=true','-DElab.async=false','-j1','-M12000',str(source)],cwd='Lean',env=dict(os.environ,LEAN_PATH=c['LEAN_PATH'],HW_IR_ABI=str(target)),capture_output=True,text=True)
record=dict(exit=r.returncode,seconds=round(time.time()-started,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),config_sha256=hashlib.sha256(config_path.read_bytes()).hexdigest(),output=r.stdout+r.stderr)
(box/(which+'-impure-abi-run.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2));raise SystemExit(r.returncode)
