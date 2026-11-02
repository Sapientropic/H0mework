from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import fcntl
import hashlib
import json
import os
import re
import shlex
import subprocess
import time

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
native = box.parent / 'native'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text())
config = load(box / 'lean-env.json')
plan = load(box / 'source-plan.json')
by = {row['module']: row for row in plan}
lock = (box / 'execute.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
state = dict(pid=os.getpid(), phase='strict source compilation', complete=0, total=len(plan), steps=[])

def save():
    state['updated_unix'] = time.time()
    target = box / 'status.json.writing'
    target.write_text(json.dumps(state, indent=2) + '\n')
    target.replace(box / 'status.json')

def invoke(label, command, *, env=None):
    start = time.time()
    log = box / (label + '.log')
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=root / 'Lean', env=dict(os.environ, LEAN_PATH=config['LEAN_PATH'], **(env or {})), stdout=stream, stderr=subprocess.STDOUT)
    record = dict(command=command, exit=result.returncode, seconds=round(time.time()-start,3), output=log.read_text())
    (box / (label + '.json')).write_text(json.dumps(record, indent=2)+'\n')
    if result.returncode or 'PANIC' in record['output']:
        raise RuntimeError(label + ': ' + record['output'][-5000:])
    return record

save()
old_ready = load(native / 'native-ready-verification.json')
assert old_ready['ready']
for path, value in old_ready['inputs'].items(): assert sha(path) == value, path
assert sha(old_ready['executable']) == old_ready['executable_sha256']
original_rows = load(native / 'original-project-inputs.json')
original_by = {row['module']: row for row in original_rows}
binding = load(native / 'source-binding.json')
assert sha(box / 'overlay/PublicDefaultActualNative.lean') == binding['source_sha256']
for row in plan: assert sha(row['source']) == row['source_sha256']


def artifact(module): return box / 'lib' / Path(module.replace('.', '/') + '.olean')
def c_path(module): return box / 'generated' / Path(module.replace('.', '/') + '.c')
def label(module): return 'module-' + str(next(i for i,row in enumerate(plan) if row['module'] == module))

def compile_one(row):
    module = row['module']
    target = artifact(module)
    c = c_path(module)
    c.parent.mkdir(parents=True, exist_ok=True)
    deps = {}
    for name in row['imports']:
        relative = Path(name.replace('.', '/') + '.olean')
        found = next(Path(p) / relative for p in config['LEAN_PATH'].split(':') if (Path(p) / relative).exists())
        deps[str(found)] = sha(found)
    receipt = box / (label(module) + '.json')
    if receipt.exists() and target.exists() and c.exists():
        prior = load(receipt)
        if prior.get('source_sha256') == row['source_sha256'] and prior.get('dependencies') == deps and prior.get('artifact_sha256') == sha(target) and prior.get('c_sha256') == sha(c):
            return
    for suffix in ['', '.private', '.server']:
        path = Path(str(target) + suffix)
        if path.is_symlink(): path.unlink()
    result = invoke(label(module), [config['binary'], '--trust=0', '-DwarningAsError=true', '-DElab.async=false', '-j1', '-M12000', '-R', str(box / 'overlay'), '-o', str(target), '-c', str(c), row['source']])
    assert sha(row['source']) == row['source_sha256']
    for path, value in deps.items(): assert sha(path) == value
    result.update(module=module, source=row['source'], source_sha256=row['source_sha256'], dependencies=deps,
        artifact_sha256=sha(target), c_sha256=sha(c), trust=0, werror=True, elab_async=False)
    receipt.write_text(json.dumps(result,indent=2)+'\n')

try:
    save()
    pending = set(by)
    done = set()
    with ThreadPoolExecutor(max_workers=3) as pool:
        running = {}
        while pending or running:
            available = [module for module in pending if all(dep not in by or dep in done for dep in by[module]['imports'])]
            for module in sorted(available):
                if len(running) == 3: break
                running[pool.submit(compile_one, by[module])] = module
                pending.remove(module)
            assert running, ('cyclic source dependencies', pending)
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                module = running.pop(future)
                future.result()
                done.add(module)
                state['complete'] = len(done)
                save()
                print('INTEGRATED STRICT',len(done),'/',len(plan),module,flush=True)
    state['phase'] = 'original logical identity'
    save()
    pairs = []
    for row in plan:
        module = row['module']
        if module in original_by: old = original_by[module]['input_olean']
        elif module == 'PublicDefaultActualNative': old = str(native / 'generated/PublicDefaultActualNative.olean')
        else:
            # The only new module is already production-certified exact counting.
            assert module.endswith('Protocol.Whole.Counting')
            continue
        pairs += [old, str(artifact(module))]
    invoke('logical-identity', [config['binary'],'--trust=0','-DwarningAsError=true','-DElab.async=false','-j1','-M12000','--run',str(box / 'identity.lean'),*pairs])
    state['phase'] = 'official native objects'
    save()
    leanc = str(Path(config['binary']).with_name('leanc'))
    def compile_object(row):
        module = row['module']; source = c_path(module); obj = source.with_suffix('.o')
        receipt = box / (label(module) + '-object.json')
        if receipt.exists() and obj.exists():
            old = load(receipt)
            if old.get('c_sha256') == sha(source) and old.get('object_sha256') == sha(obj): return
        record = invoke(label(module)+'-object',[leanc,'-c','-O2','-ffp-contract=off',*(['-Dmain=public_default_generated_main'] if module == 'PublicDefaultActualNative' else []),str(source),'-o',str(obj)])
        record.update(c_sha256=sha(source),object_sha256=sha(obj))
        receipt.write_text(json.dumps(record,indent=2)+'\n')
    with ThreadPoolExecutor(max_workers=3) as pool:
        for future in [pool.submit(compile_object,row) for row in plan]: future.result()
    extra_rows=load(box/'extra-exports-plan.json') if (box/'extra-exports-plan.json').exists() else []
    extra_by={row['moduleName']:row for row in extra_rows}
    if extra_rows:
        exported=load(box/'extra-exports.json');assert exported['exit']==0 and exported['source_sha256']==sha(box/'OriginalExports.lean')
    for i,row in enumerate(extra_rows):
        source=Path(row['path']);obj=source.with_suffix('.o');metadata=load(str(source)+'.json')
        assert row['moduleName'] not in by
        assert metadata['original_module']==row['moduleName'] and metadata['original_exported_mono_providers']==row['helpers']
        assert metadata['original_impure_abi_checked']
        record=invoke('extra-object-'+str(i),[leanc,'-c','-O2','-ffp-contract=off',str(source),'-o',str(obj)])
        record.update(c_sha256=sha(source),object_sha256=sha(obj));(box/('extra-object-'+str(i)+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    objects = [str(c_path(row['module']).with_suffix('.o')) if row['module'] in by else str(Path(extra_by[row['module']]['path']).with_suffix('.o')) if row['module'] in extra_by else str(Path(row['c']).with_suffix('.o')) for row in original_rows]
    new = [row for row in plan if row['module'] not in original_by and row['module'] != 'PublicDefaultActualNative']
    objects += [str(c_path(row['module']).with_suffix('.o')) for row in new]
    rsp = box / 'objects.rsp';rsp.write_text('\n'.join(shlex.quote(p) for p in objects)+'\n')
    old_cmd = load(native / 'native-link.json')['command']
    cmd = ['@'+str(rsp) if arg == '@'+str(native/'native-link-objects.rsp') else str(c_path('PublicDefaultActualNative').with_suffix('.o')) if arg == str(native/'generated/PublicDefaultActualNative.o') else arg for arg in old_cmd]
    exe = box / 'public-default-integrated'
    assert cmd[-2] == '-o'; cmd[-1] = str(exe)
    state['phase'] = 'strict native linking'; save()
    invoke('native-link',cmd)
    def symbols(paths,flag):
        found=set()
        for start in range(0,len(paths),64):
            output=subprocess.check_output(['nm',flag,*map(str,paths[start:start+64])],text=True)
            found.update(line for line in output.splitlines() if line.startswith('_'))
        return found
    prefix=Path(config['binary']).parent.parent
    providers=[Path(row['path']) for row in load(native/'official-package-providers.json')]
    providers += [p for p in (prefix/'lib/lean').glob('*.dylib') if p.name in ['libleanshared.dylib','libLake_shared.dylib','libInit_shared.dylib'] or p.name.startswith('libleanshared_')]
    definitions=symbols([Path(p) for p in objects]+[c_path('PublicDefaultActualNative').with_suffix('.o')]+providers,'-gUj')
    required={name for name in symbols([exe],'-uj') if name.startswith(('_l_','_lp_','_initialize_','_runtime_initialize_','_meta_initialize_','_lean_'))}
    assert not required-definitions,('missing exact linked providers before initialization',sorted(required-definitions))
    state['phase'] = 'original initialization'; save()
    invoke('native-init-only',[str(exe),'--init-only'])
    # An independent verifier must bind these objects and initialization before main.
    state['phase'] = 'awaiting independent ready verification';state['executable'] = str(exe); state['executable_sha256'] = sha(exe);save()
    print('INTEGRATED BUILD PASS: exact source strict compiles, original logical identity, native link and initialization; actual main not yet called',flush=True)
except Exception as error:
    state.update(phase='stopped at concrete diagnostic',error=str(error),exit=1);save();raise
