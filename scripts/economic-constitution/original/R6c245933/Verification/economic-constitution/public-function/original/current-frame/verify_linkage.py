from pathlib import Path
import hashlib,json
b=Path(__file__).absolute().parent
r=json.loads((b/'ready-verification.json').read_text())
assert r['ready'] and r['init_only_passed'] and r['source_compiled_modules']==125 and r['unresolved_lean_symbols']==0
for p,wanted in r['inputs'].items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==wanted,p
print('CURRENT FRAME LINKAGE RECHECK PASS: exact source/OLean/C/object/package/ownership/initializer certificate remains current')
