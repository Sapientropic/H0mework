from pathlib import Path
import fcntl
import hashlib
import json
import os
import subprocess
import time

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
load = lambda path: json.loads(path.read_text())
lock = (box / 'actual.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
ready = load(box / 'ready-verification.json')
assert ready['ready'] and ready['init_only_passed'] and not ready['executed_main']
assert sha(Path(ready['executable'])) == ready['executable_sha256']
assert all(sha(Path(path)) == wanted for path, wanted in ready['inputs'].items())
receipt = box / 'actual-run.json'
if receipt.exists():
    previous = load(receipt)
    assert previous['exit'] == 0 and previous['actual_cases'] == 12
    assert previous['executable_sha256'] == ready['executable_sha256']
    print('NATIVE ACTUAL ALREADY ACCEPTED: original two rounds; 12/12; no replay')
    raise SystemExit(0)
began = time.time()
log = box / 'actual-run.log'
with log.open('w') as stream:
    process = subprocess.Popen([ready['executable']], cwd=root / 'Lean',
        env=os.environ.copy(), stdout=stream, stderr=subprocess.STDOUT)
    active = dict(pid=process.pid, parent=os.getpid(), began_unix=began,
        executable=ready['executable'], executable_sha256=ready['executable_sha256'],
        literal_source_sha256=ready['original_literal_source_sha256'],
        backend=f"official Lean C; {ready['source_compiled_modules']} strict source modules with unchanged original types/bodies, shared event and original grant frame; {ready['reused_original_objects']} frozen native objects and {ready['original_olean_reemitted_modules']} original saved-Mono export providers", log=str(log))
    (box / 'active-run.json').write_text(json.dumps(active, indent=2) + '\n')
    print('NATIVE ORIGINAL TWO-ROUND CALL STARTED', process.pid, flush=True)
    status = process.wait()
output = log.read_text()
passed = status == 0 and output.count('\nPASS ') == 12 and \
    'DEFAULT ACTUAL CONTINUATION CONSUMER PASS: 12/12' in output
assert sha(Path(ready['executable'])) == ready['executable_sha256']
result = dict(exit=status, accepted=passed, actual_cases=12 if passed else 0,
    seconds=round(time.time() - began, 3), source=load(box / 'source-binding.json')['source'],
    source_sha256=ready['original_literal_source_sha256'], executable_sha256=ready['executable_sha256'],
    ready_verification_sha256=sha(box / 'ready-verification.json'),
    backend=active['backend'], output=output)
receipt.write_text(json.dumps(result, indent=2) + '\n')
print(output, end='', flush=True)
print('NATIVE ACTUAL SECONDS', result['seconds'], flush=True)
if not passed:
    raise SystemExit(status or 1)
