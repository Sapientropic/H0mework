from pathlib import Path
import hashlib,json,os,re,subprocess,time
b=Path(__file__).absolute().parent;root=Path('runtime/Documents/Homework');prior=b.parent/'temporal-frame';load=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
c=load(b/'lean-env.json');binding=load(prior/'source-binding.json');source=root/binding['source'];assert sha(source)==binding['source_sha256']
p=b/'literal-preflight';p.mkdir(exist_ok=True);alias=p/'PublicDefaultActualNative.lean'
if alias.is_symlink():alias.unlink()
literal=source.read_bytes()
if alias.exists():assert alias.read_bytes()==literal
else:alias.write_bytes(literal)
assert alias.read_bytes()==literal;artifact=p/'PublicDefaultActualNative.olean';code=p/'PublicDefaultActualNative.c';imports={}
for name in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
 rel=Path(name.replace('.','/')+'.olean');f=next(Path(x)/rel for x in c['LEAN_PATH'].split(':') if (Path(x)/rel).exists());imports[str(f)]=sha(f)
cmd=[c['binary'],'--trust=0','-DwarningAsError=true','-DElab.async=false','-j1','-M12000','-R',str(p),'-o',str(artifact),'-c',str(code),str(alias)]
began=time.time()
with (p/'compile.log').open('w') as out:r=subprocess.run(cmd,cwd=root/'Lean',env=dict(os.environ,LEAN_PATH=c['LEAN_PATH']),stdout=out,stderr=subprocess.STDOUT)
assert r.returncode==0,(p/'compile.log').read_text()
assert sha(source)==binding['source_sha256'] and all(sha(f)==h for f,h in imports.items())
reference=b.parent/'shared-runtime/generated/PublicDefaultActualNative.c';same=code.read_bytes()==reference.read_bytes()
record=dict(accepted=same,exit=r.returncode,command=cmd,source=str(source),source_sha256=sha(source),artifact=str(artifact),artifact_sha256=sha(artifact),complete_c=str(code),complete_c_sha256=sha(code),reference_complete_c=str(reference),reference_complete_c_sha256=sha(reference),complete_module_c_byte_identical=same,imports=imports,seconds=round(time.time()-began,3),script_sha256=sha(Path(__file__)),executed_main=False)
(b/'literal-preflight.json').write_text(json.dumps(record,indent=2)+'\n')
assert same,'new current frame candidate changes the complete original literal C'
print('CURRENT FRAME LITERAL PREFLIGHT PASS: original source strict compile; complete C byte-identical to the original actual main; consumer not invoked')
