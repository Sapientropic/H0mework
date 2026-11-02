from pathlib import Path
import hashlib
import json

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
load = lambda path: json.loads(path.read_text())
ready = load(box / 'ready-verification.json')
actual = load(box / 'actual-run.json')
binding = load(box / 'source-binding.json')
assert ready['ready'] and ready['original_logical_modules_preserved'] == 73 and ready['source_compiled_modules'] == 74 and ready['reused_original_objects'] == 1073 and ready['original_olean_reemitted_modules'] == 1
assert ready['unresolved_lean_symbols'] == 0 and ready['official_package_libraries'] == 8
assert sha(Path(ready['executable'])) == ready['executable_sha256'] == actual['executable_sha256']
assert actual['ready_verification_sha256'] == sha(box / 'ready-verification.json')
assert all(sha(Path(path)) == wanted for path, wanted in ready['inputs'].items())
assert actual['exit'] == 0 and actual['accepted'] and actual['actual_cases'] == 12
assert actual['output'] == (box / 'actual-run.log').read_text()
assert actual['output'].count('\nPASS ') == 12
assert 'DEFAULT ACTUAL CONTINUATION CONSUMER PASS: 12/12' in actual['output']
assert 'FAIL ' not in actual['output'] and 'PANIC' not in actual['output']
assert actual['source_sha256'] == binding['source_sha256'] == ready['original_literal_source_sha256']
assert sha(root / actual['source']) == actual['source_sha256']
result = dict(accepted=True, original_literal_consumer=True, actual_cases=12,
    source_sha256=actual['source_sha256'], executable_sha256=actual['executable_sha256'],
    actual_receipt_sha256=sha(box / 'actual-run.json'), actual_seconds=actual['seconds'],
    native_input_verification_sha256=sha(box / 'ready-verification.json'),
    frozen_original_ir_receipt_not_substituted=True, goal_complete=False)
(box / 'actual-verification.json').write_text(json.dumps(result, indent=2) + '\n')
print('NATIVE ACTUAL INDEPENDENT PASS: original literal public default; actual rounds=2; checks=12/12')
print('INTEGRATED INPUTS PASS: 74 strict source compiles; 73 original logical modules preserved; 1073 frozen object providers and one original saved-Mono export provider; full source initialization; 8 official package libraries; unresolved Lean symbols=0')
