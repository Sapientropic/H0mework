from pathlib import Path
import hashlib,json,re
b=Path(__file__).absolute().parent;load=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=load(b/'hot-source-plan.json');tables={};inputs={}
for version,cfg in [('old',b.parent/'lifecycle-frame/runtime/lean-env.json'),('new',b/'lean-env.json')]:
 run=load(b/(version+'-impure-abi-run.json'))
 assert run['exit']==0 and run['source_sha256']==sha(b/'impure-abi.lean') and run['config_sha256']==sha(cfg)
 data=load(b/(version+'-impure-abi.json'));assert sha(b/(version+'-impure-abi.json'))==run['output_sha256']
 assert {r['module']:r['package'] for r in data['modules']}=={r['module']:r['package'] for r in rows}
 for p,h in run['imports'].items():assert sha(p)==h,p;inputs[p]=h
 inputs[str(b/(version+'-impure-abi-run.json'))]=sha(b/(version+'-impure-abi-run.json'));inputs[str(b/(version+'-impure-abi.json'))]=run['output_sha256']
 tables[version]={r['name']:r for r in data['declarations']};assert len(tables[version])==len(data['declarations'])
old,new=tables['old'],tables['new']
changed={n for n in old.keys()&new.keys() if any(old[n][k]!=new[n][k] for k in ['symbol','params','result'])};removed=old.keys()-new.keys();symbols={old[n]['symbol'] for n in changed|removed}
sources=load(b/'c-sources.json');fresh={str(b/'generated'/Path(r['module'].replace('.','/')+'.c')) for r in rows};uses=[]
pattern=re.compile(r'\b(?:l|lp)_[A-Za-z0-9_]+\b')
for p in sources:
 inputs[p]=sha(p)
 for lineno,line in enumerate(Path(p).read_text().splitlines(),1):
  for symbol in set(pattern.findall(line))&symbols:
   if re.match(r'^(?:(?:LEAN_EXPORT|extern|static) )?(?:lean_object\*|uint\w+|size_t|double|float) '+re.escape(symbol)+r'\(',line):continue
   assert p in fresh,('stale owned/borrowed caller or removed helper',p,lineno,symbol)
   uses.append(dict(source=p,line=lineno,symbol=symbol))
inputs[str(b/'impure-abi.lean')]=sha(b/'impure-abi.lean');inputs[str(b/'emit_impure_abi.py')]=sha(b/'emit_impure_abi.py');inputs[str(b/'verify_ownership.py')]=sha(b/'verify_ownership.py')
record=dict(accepted=True,modules=len(rows),old_declarations=len(old),new_declarations=len(new),changed_ownership_signatures=sorted(changed),removed_ir_helpers=sorted(removed),refreshed_call_sites=uses,inputs=inputs)
(b/'ownership-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'ROOT FRAME OWNERSHIP CHECK PASS: modules={len(rows)}; old/new IR={len(old)}/{len(new)}; changed={len(changed)}; removed={len(removed)}; stale call sites=0')
