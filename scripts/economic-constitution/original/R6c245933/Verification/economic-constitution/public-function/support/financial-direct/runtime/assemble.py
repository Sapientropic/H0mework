from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import shlex
import subprocess
import time

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
base = box.parents[1]
shared = base / 'shared-runtime'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text())
config = load(box / 'lean-env.json')
env = dict(os.environ, LEAN_PATH=config['LEAN_PATH'])
state = dict(pid=os.getpid(), phase='verify frozen inputs', steps=[])

def save():
    state['updated_unix'] = time.time()
    pending = box / 'assembly-status.json.writing'
    pending.write_text(json.dumps(state, indent=2) + '\n')
    pending.replace(box / 'assembly-status.json')

def invoke(label, command):
    started = time.time()
    with (box / (label + '.log')).open('w') as output:
        result = subprocess.run(command, cwd=root/'Lean', env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    record = dict(command=command, exit=result.returncode,
                  seconds=round(time.time()-started, 3),
                  output=(box/(label+'.log')).read_text())
    (box/(label+'.json')).write_text(json.dumps(record, indent=2)+'\n')
    if result.returncode:
        raise RuntimeError(label + ': ' + record['output'][-4000:])
    return record

try:
    save()
    ready = load(shared/'ready-verification.json')
    assert ready['ready'] and ready['init_only_passed']
    for path, wanted in ready['inputs'].items(): assert sha(path) == wanted, path
    assert load(box.parent/'direct-kernel-run.json')['exit'] == 0
    original_objects = shlex.split((shared/'objects.rsp').read_text())
    originals = {r['module']: r for r in load(base/'native/original-project-inputs.json')}
    replacements = {}
    pairs = []
    for label in ['DirectCompletion', 'DirectReplacement', 'DirectEvent']:
        receipt = load(box/(label+'-compile.json'))
        assert receipt['exit'] == 0 and receipt['exact_dependencies']
        assert receipt['compile_options'] == dict(trust=0, werror=True, elab_async=False, threads=1, memory_mb=12000)
        module = receipt['module']
        source = root/receipt['source']
        artifact = box/'lib'/Path(module.replace('.', '/')+'.olean')
        c = Path(receipt['c_path'])
        assert sha(source) == receipt['source_sha256']
        assert sha(artifact) == receipt['artifact_sha256']
        assert sha(c) == receipt['c_sha256']
        assert all(sha(next(Path(p)/Path(name.replace('.', '/')+'.olean') for p in config['LEAN_PATH'].split(':')
                            if (Path(p)/Path(name.replace('.', '/')+'.olean')).exists())) == wanted
                   for name, wanted in receipt['dependencies'].items())
        old_object = next(p for p in original_objects if p.endswith(module.replace('.', '/')+'.o'))
        replacements[old_object] = str(c.with_suffix('.o'))
        pairs += [originals[module]['input_olean'], str(artifact)]
    completion = load(box/'DirectCompletion-compile.json')['module']
    relative = Path(completion.replace('.', '/')+'.olean')
    pairs += [str(box.parent/'lib'/relative), str(box/'lib'/relative)]
    state['phase'] = 'complete original identity and certified proof reuse'; save()
    invoke('linked-identity', [config['binary'], '--trust=0', '-DwarningAsError=true',
        '-DElab.async=false', '-j1', '-M12000', '--run', str(box/'linked-identity.lean'), *pairs])
    objects = [replacements.get(p, p) for p in original_objects]
    sources = [str(Path(p).with_suffix('.c')) for p in objects]
    sources += [str(shared/'generated/PublicDefaultActualNative.c'), str(base/'native/NativeBoot.c')]
    (box/'c-sources.json').write_text(json.dumps(sources, indent=2)+'\n')
    state['phase'] = 'full linked C ABI'; save()
    invoke('c-abi-negative-controls', ['python3', str(box/'check_c_abi.py'), '--self-test'])
    invoke('c-abi', ['python3', str(box/'check_c_abi.py')])
    state['phase'] = 'three official native objects'; save()
    leanc = str(Path(config['binary']).with_name('leanc'))
    def compile_object(pair):
        old, target = pair
        obj = Path(target); c = obj.with_suffix('.c')
        label = 'object-'+obj.stem
        receipt = box/(label+'.json')
        if receipt.exists() and obj.exists():
            paid = load(receipt)
            if paid.get('c_sha256') == sha(c) and paid.get('object_sha256') == sha(obj): return
        record = invoke(label, [leanc, '-c', '-O2', '-ffp-contract=off', str(c), '-o', str(obj)])
        record.update(c_sha256=sha(c), object_sha256=sha(obj))
        receipt.write_text(json.dumps(record, indent=2)+'\n')
    with ThreadPoolExecutor(max_workers=3) as pool:
        list(pool.map(compile_object, replacements.items()))
    rsp = box/'objects.rsp'; rsp.write_text('\n'.join(shlex.quote(p) for p in objects)+'\n')
    cmd = load(shared/'native-link.json')['command']
    cmd = ['@'+str(rsp) if arg == '@'+str(shared/'objects.rsp') else arg for arg in cmd]
    exe = box/'public-default-direct'; assert cmd[-2] == '-o'; cmd[-1] = str(exe)
    state['phase'] = 'strict native link'; save()
    invoke('native-link', cmd)
    state['phase'] = 'initialization pending independent symbol verification'
    state.update(executable=str(exe), executable_sha256=sha(exe), replacements=replacements)
    save()
except Exception as error:
    state.update(exit=1, phase='stopped at concrete diagnostic', error=str(error)); save(); raise
