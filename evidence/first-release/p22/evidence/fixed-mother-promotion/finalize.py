from pathlib import Path
import json,hashlib,re,subprocess
r=Path.cwd(); c=r/'.cache/fixed-mother-promotion'; a=r/'.cache/fixed-mother-certification';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cap=r/'.cache/fixed-mother-theorem/capsule.json';capsule=json.loads(cap.read_text());p=r/capsule['parent_production_manifest'];parent=json.loads(p.read_text());m=json.loads((c/'manifest.json').read_text())
assert sha(cap)=='640fe14ce21eaffa176e614b0cf24d146a4ccb4f2dd2fe1d03b637b7dbe41fac';assert sha(p)==capsule['parent_production_manifest_sha256']
for i in parent['all_files']:
 assert sha(r/i['production'])==i['production_sha256'];assert sha(Path(i['production_olean']))==i['production_olean_sha256']
for i in m['files']:
 assert sha(r/i['candidate'])==i['candidate_sha256'];assert sha(r/i['production'])==i['production_sha256']
 source=(r/i['candidate']).read_text()
 for j in m['files']:source=source.replace('import '+j['candidate_module']+'\n','import '+j['production_module']+'\n')
 assert source==(r/i['production']).read_text()
def latest(cache,stem):
 candidates=[]
 for q in cache.glob(stem+'-*.json'):
  v=json.loads(q.read_text())
  if v.get('exit_code')==0 and sha(r/v['source'])==v['sha256']:
   assert v['source_unchanged'] and v['parent_329_source_olean_unchanged'];assert sha(Path(v['olean']))==v['olean_sha256'];candidates.append((int(q.stem.rsplit('-',1)[1]),q,v))
 assert candidates,stem
 _,q,v=max(candidates);return q,v
selected=[]
for cache,stems in [(a,['Formation','CompleteRealization','Audit','Consumers']),(c,['Formation','CompleteRealization','Parity','MotherFixedSourceRealization','MotherFixedSourceRealizationConsumer'])]:
 for stem in stems:selected.append(latest(cache,stem))
for q,v in selected:
 log=(r/v['log']).read_text()
 if q.stem.startswith('Audit') or q.stem.startswith('MotherFixedSourceRealization-'):
  assert 'own=64 closure=82345 edges=2459064' in log
 if q.stem.startswith('Consumers') or q.stem.startswith('MotherFixedSourceRealizationConsumer-'):
  assert 'count=5 single_mouth=1 closure=82768 edges=2469334' in log
 if q.stem.startswith('Parity'):
  assert 'own=64 complete_type_value_metadata=1 full_closure=82345 full_edges=2459064' in log
for i in m['files']:
 q,v=latest(c,Path(i['production']).stem);i.update(production_olean=str(Path(v['olean']).relative_to(r)),production_olean_sha256=v['olean_sha256'])
subprocess.run(['git','diff','--check'],check=True)
d=r/'docs/audits/physics/source-uniqueness';sources=[i['production'] for i in m['files']];artifacts=[str((d/x).relative_to(r)) for x in ['MotherFixedSourceRealization.lean','MotherFixedSourceRealizationConsumer.lean','MotherFixedSourceRealization.md']]
preserved=['SaturationMonoid/PhysicsCore/Stage9C/Revision/SpinPair/Source.lean','SaturationMonoid/PhysicsCore/Stage10/SourceUniqueness/Formation/Family/Occurrence/Trace.lean','SaturationMonoid/PhysicsCore/Stage10/Runtime/Occurrence.lean','SaturationMonoid/PhysicsCore/Stage10/Runtime/Activation.lean']
for f in preserved:
 assert (r/f).read_bytes()==subprocess.check_output(['git','show','HEAD:Lean/'+f])
parent_durable={str(f.relative_to(r)):sha(f) for f in sorted(d.glob('*.certification.json')) if f.name!='MotherFixedSourceRealization.certification.json'}
report={
 'verdict':'certified-production','public_mouth':capsule['public_mouth'],'mouth_outer_arity':0,
 'scope':'One theorem on the unchanged original Type0 lawful-world, complete inquiry, and complete macro-process domains. Each existential origin carries its actual material in the closure of the fixed MotherRoot finite evaluator image, actual source-factory binding, full record recovery and original consumers. All parent material spaces retained. Existing sealed activation law/runtime transported.',
 'phase':'independent lean-certify; import-only production promotion',
 'lean_version':'4.33.0','lean_sha256':parent['lean_sha256'],'flags':['--trust=0','-DwarningAsError=true'],
 'capsule_sha256':sha(cap),'parent_promotion_manifest_sha256':sha(p),'parent_production_modules_unchanged':329,
 'parent_durable_certificates':parent_durable,'files':m['files'],'only_import_edits':True,'new_admission_or_representation_premises':False,
 'parity':{'new_modules':2,'own_declarations':64,'full_type_value_metadata':True,'complete_metadata_dependencies':True,'closure_nodes':82345,'closure_edges':2459064,'shared_same_module_olean_nodes':82281,'owner_and_edge_bijection':True,'universe_structure_positive_and_negative_controls':True,'registered_instances':0,'codegen_only':0},
 'trust':{'axioms':['propext','Classical.choice','Quot.sound'],'unsafe':0,'trusted_partial':0,'production_scratch_imports':0},
 'consumers':{'count':5,'proof_values_directly_reference_single_mouth':True,'direct_old_source_bypass_rejected':True,'original_arbitrary_domains':3,'original_complete_activation':True,'original_sealed_ask_and_whole_law':True,'original_tick_16_to_17_and_all_finite_history':True,'closure_nodes':82768,'closure_edges':2469334,'axioms':['propext','Classical.choice','Quot.sound'],'unsafe':0,'trusted_partial':0},
 'shared_import_bindings':{'modules':3097,'sha256':sha(c/'shared-owner-oleans.json'),'cache':str((c/'shared-owner-oleans.json').relative_to(r)),'same_search_path_in_both_environments':True},
 'preserved_original_sources':{f:sha(r/f) for f in preserved},
 'receipts':{str(q.relative_to(r)):sha(q) for q,v in selected},
 'audit_sources':{str(f.relative_to(r)):sha(f) for f in [a/'run.py',a/'prepare_audit.py',a/'add_consumer_audit.py',a/'Audit.lean',a/'Consumers.lean',c/'prepare.py',c/'link_parent.py',c/'make_parity.py',c/'Parity.lean',c/'finalize.py']},
 'artifacts':{f:sha(r/f) for f in artifacts},
 'git':{'index_modified_by_certifier':False,'commit_created_by_certifier':False,'main_modified_by_certifier':False,'old_production_unchanged':True,'diff_check':True}}
(c/'promotion-manifest.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n'); (d/'MotherFixedSourceRealization.certification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
owned=sources+artifacts+[str((d/'MotherFixedSourceRealization.certification.json').relative_to(r))]
(c/'owned-files.json').write_text(json.dumps({f:sha(r/f) for f in owned},indent=2)+'\n')
print(json.dumps({'verdict':report['verdict'],'production_modules':2,'own':64,'consumer':5,'owned_files':{f:sha(r/f) for f in owned}},indent=2))
