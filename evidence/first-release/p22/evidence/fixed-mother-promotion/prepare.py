from pathlib import Path
import hashlib,json,re
r=Path.cwd(); c=r/'.cache/fixed-mother-promotion'; capsule=json.loads((r/'.cache/fixed-mother-theorem/capsule.json').read_text()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
items=[]
mapping={x['file'].removesuffix('.lean').replace('/','.'):p.removesuffix('.lean').replace('/','.') for x,p in zip(capsule['files'],capsule['production_targets'])}
for item,target in zip(capsule['files'],capsule['production_targets']):
 p=r/item['file']; assert sha(p)==item['sha256']; s=p.read_text(); original=s; edits=[]
 for old,new in mapping.items():
  match=re.search(r'^import '+re.escape(old)+r'$',s,re.M)
  if match:
   edits.append((len(s[:match.start()+7].encode()),len(s[:match.end()].encode()),len(new.encode())))
   s=s[:match.start()+7]+new+s[match.end():]
 out=r/target;out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();out.write_text(s)
 items.append({'candidate':item['file'],'candidate_module':item['file'].removesuffix('.lean').replace('/','.'),'candidate_sha256':sha(p),'production':target,'production_module':target.removesuffix('.lean').replace('/','.'),'production_sha256':sha(out),'edits':edits})
(c/'manifest.json').write_text(json.dumps({'parent_manifest':capsule['parent_production_manifest'],'parent_sha256':capsule['parent_production_manifest_sha256'],'files':items,'only_import_edits':True},indent=2)+'\n')
# Reuse the exact already-passing trust and consumer audits with only import/owner relocation.
def relocate(s):
 for a,b in mapping.items():s=s.replace(a,b)
 return s
for src,dst in [('Audit.lean','MotherFixedSourceRealization.lean'),('Consumers.lean','MotherFixedSourceRealizationConsumer.lean')]:
 s=relocate((r/'.cache/fixed-mother-certification'/src).read_text())
 s=s.replace('.cache/fixed-mother-certification/own-names.json','.cache/fixed-mother-promotion/own-names.json').replace('.cache/fixed-mother-certification/closure-names.json','.cache/fixed-mother-promotion/closure-names.json')
 if src=='Audit.lean':
  s=s.replace(' && !modules.contains module','')
 else:
  s=s.replace('  let env ← getEnv\n','  let env ← getEnv\n  for module in env.header.moduleNames do\n    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"\n',1)
 (r/'docs/audits/physics/source-uniqueness'/dst).write_text(s)
print('PREPARED',len(items),'production files and two durable audit/consumer files')
