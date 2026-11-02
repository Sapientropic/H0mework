from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from types import SimpleNamespace
import fcntl

box = Path(__file__).absolute().parent
root = Path('runtime/Documents/Homework')
config = json.loads(Path(os.environ.get('HW_LEAN_CONFIG', str(box / 'lean-env.json'))).read_text())
module = sys.argv[1].replace("/", ".")
setup_path = config.get('module_setups',{}).get(module)
setup_sha256 = hashlib.sha256(Path(setup_path).read_bytes()).hexdigest() if setup_path else None
run_main = len(sys.argv) > 3 and sys.argv[3] == 'run'
relative = Path(module.replace('.', '/') + '.lean')
source_root = box / 'overlay' if (box / 'overlay' / relative).exists() else root / 'Lean'
source = source_root / relative
artifact = box / 'lib' / relative.with_suffix('.olean')
with (box / 'materialize.lock').open('a') as materialization_lock:
    fcntl.flock(materialization_lock, fcntl.LOCK_EX)
    component = box/'lib'
    for part in artifact.parent.relative_to(component).parts:
        component = component/part
        if component.is_symlink():
            prior = component.resolve()
            entries = list(prior.iterdir())
            component.unlink()
            component.mkdir()
            for entry in entries: (component/entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
        else: component.mkdir(exist_ok=True)
    artifact.parent.mkdir(parents=True, exist_ok=True)
c=box/'generated'/relative.with_suffix('.c')
c.parent.mkdir(parents=True,exist_ok=True)
lock_path = box / (module + '.lock')
compile_lock = lock_path.open('w')
fcntl.flock(compile_lock, fcntl.LOCK_EX)
shared_index = box / 'shared-receipt-index.json'
shared = json.loads(shared_index.read_text()).get(module, []) if shared_index.exists() else []
for prior in [] if os.environ.get('HW_FORCE_RECOMPILE') else list(box.glob('*-compile.json')) + [Path(path) for path in shared]:
    cached = json.loads(prior.read_text())
    if cached.get('setup_sha256') != setup_sha256:
        continue
    if cached.get('module') != module or cached.get('exit') != 0 or not artifact.exists() or (run_main and not cached.get('executed_main')):
        continue
    if cached['source_sha256'] != hashlib.sha256(source.read_bytes()).hexdigest() or cached['artifact_sha256'] != hashlib.sha256(artifact.read_bytes()).hexdigest():
        continue
    actual_dependencies = {}
    for name in cached['dependencies']:
        file = next((Path(path) / (name.replace('.', '/') + '.olean')
            for path in config['LEAN_PATH'].split(os.pathsep)
            if (Path(path) / (name.replace('.', '/') + '.olean')).exists()), None)
        actual_dependencies[name] = hashlib.sha256(file.read_bytes()).hexdigest() if file else None
    if actual_dependencies != cached['dependencies']:
        continue
    print(json.dumps(dict(reused_exact_receipt=str(prior),module=module,exit=0)),flush=True)
    raise SystemExit(0)
for suffix in ['', '.private', '.server']:
    linked = Path(str(artifact) + suffix)
    if linked.is_symlink():
        linked.unlink()
label = sys.argv[2] if len(sys.argv) > 2 else module.split('.')[-1]
assert re.fullmatch(r'[A-Za-z0-9_-]+', label), label
log = box / (label + '.log')
receipt_path = box / (label + '-compile.json')
digest = hashlib.sha256(source.read_bytes()).hexdigest()
roots = [Path(path) for path in config['LEAN_PATH'].split(os.pathsep)]
dependencies = {}
for imported in re.findall(r'^import\s+(\S+)', source.read_text(), re.M):
    file = next(path / (imported.replace('.', '/') + '.olean') for path in roots
                if (path / (imported.replace('.', '/') + '.olean')).exists())
    dependencies[imported] = hashlib.sha256(file.read_bytes()).hexdigest()
started = time.time()
with log.open('w') as output:
    try:
        result = subprocess.run([config['binary'], '--trust=0', '-DwarningAsError=true',
        '-DElab.async=false', '-j1', '-M12000', *(['--setup='+setup_path] if setup_path else []), '-R', str(source_root),
        *(['-Dprofiler=true'] if len(sys.argv) > 3 and sys.argv[3] == 'profile' else []),
        '-o', str(artifact), '-c', str(c), *(['--run'] if run_main else []), str(source)], cwd=root / 'Lean',
        env=dict(os.environ, LEAN_PATH=config['LEAN_PATH']), stdout=output, stderr=subprocess.STDOUT,
        timeout=1800)
    except subprocess.TimeoutExpired:
        result = SimpleNamespace(returncode=124)
assert hashlib.sha256(source.read_bytes()).hexdigest() == digest
for imported, expected in dependencies.items():
    file = next(path / (imported.replace('.', '/') + '.olean') for path in roots
                if (path / (imported.replace('.', '/') + '.olean')).exists())
    assert hashlib.sha256(file.read_bytes()).hexdigest() == expected, imported
receipt = dict(module=module, setup_sha256=setup_sha256, module_package=json.loads(Path(setup_path).read_text()).get('package') if setup_path else None, source=str(source.relative_to(root)), source_sha256=digest,
               exit=result.returncode, seconds=round(time.time() - started, 3),
               compile_options=dict(trust=0, werror=True, elab_async=False, threads=1, memory_mb=12000),
               dependencies=dependencies, exact_dependencies=True, executed_main=run_main, output=log.read_text())
if result.returncode == 0:
    receipt['artifact_sha256'] = hashlib.sha256(artifact.read_bytes()).hexdigest()
    receipt['c_path'] = str(c)
    receipt['c_sha256'] = hashlib.sha256(c.read_bytes()).hexdigest()
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, ensure_ascii=False, indent=2), flush=True)
raise SystemExit(result.returncode)
