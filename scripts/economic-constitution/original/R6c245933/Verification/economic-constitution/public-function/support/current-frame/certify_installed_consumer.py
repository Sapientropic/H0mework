from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

root=Path('runtime/Documents/Homework')
box=Path(__file__).absolute().parent
prod=box/'production'
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
conf=load(prod/'lean-env.json')
ready=load(box/'ready-verification.json')
actual=load(box/'actual-run.json')
assert actual['exit']==0 and actual['accepted'] and actual['actual_cases']==12
assert actual['executable_sha256']==ready['executable_sha256']
source=root/'Lean/scripts/verification/public-source-owned-iteration-consumer.lean'
assert sha(source)==actual['source_sha256']==ready['original_literal_source_sha256']
# Keep the original compiler module name while reading the installed source.
source_root=prod/'consumer-source'
source_root.mkdir(exist_ok=True)
alias=source_root/'PublicDefaultActualNative.lean'
# Lean resolves symlinks before enforcing -R; preserve the original module
# name with an exact source copy inside the compiler root.
if alias.is_symlink():alias.unlink()
literal=source.read_bytes()
if alias.exists():assert alias.read_bytes()==literal
else:alias.write_bytes(literal)
assert not alias.is_symlink() and alias.read_bytes()==literal
artifact=prod/'lib/PublicDefaultActualNative.olean'
c=prod/'installed-consumer.c'
for suffix in ['', '.private', '.server']:
    output=Path(str(artifact)+suffix)
    if output.is_symlink():output.unlink()
imports={}
for module in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
    relative=Path(module.replace('.','/')+'.olean')
    path=next(Path(base)/relative for base in conf['LEAN_PATH'].split(':') if (Path(base)/relative).exists())
    imports[str(path)]=sha(path)
command=[conf['binary'],'--trust=0','-DwarningAsError=true','-DElab.async=false','-j1','-M12000','-R',str(source_root),'-o',str(artifact),'-c',str(c),str(alias)]
start=time.time()
with (prod/'installed-consumer-compile.log').open('w') as stream:
    result=subprocess.run(command,cwd=root/'Lean',env=dict(os.environ,LEAN_PATH=conf['LEAN_PATH']),stdout=stream,stderr=subprocess.STDOUT)
assert result.returncode==0,(prod/'installed-consumer-compile.log').read_text()
for path,value in imports.items():assert sha(path)==value
assert sha(source)==actual['source_sha256'] and sha(alias)==sha(source)
reference=box.parent/'shared-runtime/lib/PublicDefaultActualNative.olean'
reference_c=box.parent/'shared-runtime/generated/PublicDefaultActualNative.c'
assert sha(reference)==ready['inputs'][str(reference)]
assert sha(reference_c)==ready['inputs'][str(reference_c)]
identity_command=[conf['binary'],'--trust=0','-DwarningAsError=true','-DElab.async=false','-j1','-M12000','--run',str(box/'linked-identity.lean'),str(reference),str(artifact)]
with (prod/'installed-consumer-identity.log').open('w') as stream:
    identity=subprocess.run(identity_command,cwd=root/'Lean',env=dict(os.environ,LEAN_PATH=conf['LEAN_PATH']),stdout=stream,stderr=subprocess.STDOUT)
assert identity.returncode==0,(prod/'installed-consumer-identity.log').read_text()
# Full C byte identity covers run, main, every emitted helper, codegen attributes,
# and the entire ordered module initializer, not merely the entry point.
assert c.read_bytes()==reference_c.read_bytes(),'installed consumer C differs from the already executed complete module'
record=dict(accepted=True,source=str(source.relative_to(root)),source_sha256=sha(source),command=command,
    exit=0,seconds=round(time.time()-start,3),trust=0,werror=True,elab_async=False,
    imports=imports,artifact=str(artifact),artifact_sha256=sha(artifact),reference_artifact_sha256=sha(reference),
    complete_c=str(c),complete_c_sha256=sha(c),executed_complete_c_sha256=sha(reference_c),
    complete_module_c_byte_identical=True,identity_output=(prod/'installed-consumer-identity.log').read_text(),
    reused_actual_receipt_sha256=sha(box/'actual-run.json'),actual_cases=12,
    verification_script_sha256=sha(Path(__file__)))
(prod/'installed-consumer-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('INSTALLED ACTUAL CONSUMER PASS: strict source compile; all original logical declarations; complete emitted C byte-identical to the module executed in the accepted two-round 12/12 call',flush=True)
