from pathlib import Path
import argparse,copy,hashlib,json,os,stat,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[3]
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
import source_view as sv

def read(p):return json.loads(p.read_bytes())
def encoded(v,indent=1,sort=True):return (json.dumps(v,ensure_ascii=False,indent=indent,sort_keys=sort)+'\n').encode()
def like(path,old,new):
 raw=path.read_bytes()
 for indent in (1,2,4):
  for sort in (False,True):
   if encoded(old,indent,sort)==raw:return encoded(new,indent,sort)
 if path.is_relative_to(ROOT/'.local'):return encoded(new,2,False)
 raise ValueError('Unrecognized JSON format: '+str(path))
def atomic(path,raw):
 path.parent.mkdir(parents=True,exist_ok=True)
 mode=stat.S_IMODE(path.stat().st_mode) if path.exists() else 0o644
 with tempfile.NamedTemporaryFile(dir=path.parent,prefix='.'+path.name+'.',delete=False) as f:
  temp=Path(f.name);os.fchmod(f.fileno(),mode);f.write(raw)
 os.replace(temp,path)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--apply',action='store_true');args=ap.parse_args()
 marker=read(BASE.parent/'cohort-freeze.json');head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
 assert head==marker['head']=='62da11e06ce55da48c1d8e6b8be8bd6047040eae'
 if args.apply:assert marker['official_dispatch_hold']
 assert sv.sha((ROOT/'docs/first-release-map.json').read_bytes())=='70a109c44e4fa0907f817e5ff7751029562415d82b0a1b48cb854053aeba78be'
 plan=read(BASE/'candidate-plan.json');assert plan['candidate_inverse_passed']==4
 assert not read(BASE/'existing-input-original-import-bindings.json')['ordered_original_import_token_or_dependency_identity_mismatches']
 assert not read(BASE/'additional-input-original-import-bindings.json')['mismatches']
 resources=read(BASE/'existing-input-resources-fixed-c62.json');assert len(resources['fixed_git_sha_verified'])==23 and not resources['actual_digest_mismatch'] and not resources['non_git_retained_resource_bindings']
 ep=ROOT/'tools/export-map.json';sp=ROOT/'.local/migration/state2.json';mp=ROOT/'docs/low-energy-release-map.json'
 exported,state,data=read(ep),read(sp),read(mp);old_export,old_state,old_map=copy.deepcopy(exported),copy.deepcopy(state),copy.deepcopy(data)
 ref=plan['source_epoch'];pid=plan['package_id'];aggregate=plan['lean_target']
 public={r['target']:r for r in exported['modules']};stored={r.get('target_module',r.get('target')):r for k in ['files','explicit_files'] for r in state[k]}
 members=read(BASE/'existing-input-module-membership.json');paths=[];added_epochs=[]
 for module in members:
  row=public[module];private=stored[module];assert row['source_sha256']==private['source_sha256']
  paths.append(row['source_path'])
  if ref not in row['source_revisions']:
   row['source_revisions'].append(ref);private['source_revisions'].append(ref);added_epochs.append(module)
 changes={};rows=read(BASE/'candidate-module-rows.json')
 for row in rows:
  assert row['target'] not in public and not (ROOT/row['path']).exists()
  raw=(BASE/'candidate-root'/row['path']).read_bytes();assert sv.sha(raw)==row['target_sha256']
  changes[row['path']]=raw;exported['modules'].append(row);public[row['target']]=row;paths.append(row['source_path'])
  p=copy.deepcopy(row);p['source_module']=p.pop('source');p['target_module']=p.pop('target');p['transformed_sha256']=p.pop('target_sha256');state['explicit_files'].append(p)
 agg=plan['new_aggregator'];assert aggregate not in exported['paper_aggregators'];changes[agg['path']]=(BASE/'candidate-root'/agg['path']).read_bytes();assert sv.sha(changes[agg['path']])==agg['sha256']
 exported['paper_aggregators'][aggregate]=agg['path'];state['paper_aggregators'][aggregate]=agg
 artifact=read(BASE/'candidate-artifact-row.json');assert not any(r['path']==artifact['path'] for r in exported['artifacts']);exported['artifacts'].append(artifact);state['artifacts'].append(copy.deepcopy(artifact));changes[artifact['path']]=(BASE/'candidate-root'/artifact['path']).read_bytes()
 claim=read(BASE/'candidate-L23-claim.json')
 for role in ['producers','direct_consumers','resources','import_bridges']:
  for entry in claim[role]:
   entry['verification']['identity']='mapped'
   if 'owner_selection' in entry:entry['owner_selection']['scope']='Exact fixed source identity and actual registered package imports.'
 data['claims']=[claim if c['id']=='low1.L23' else c for c in data['claims']]
 oldpkg=next(p for p in data['proof_packages'] if p['id']=='low-energy-l21-l23-e055');assert oldpkg['verification']['kernel']=='pending';oldpkg['claim_ids'].remove('low1.L23')
 package={'id':pid,'paper':'low-energy-phenomenology','source_commit':ref,'source_commits':[ref],'claim_ids':['low1.L23'],'lean_target':aggregate,'verification':{'build':'pending','kernel':'pending','scope':'Revised L23 fixed-source producer and full-light direct consumer; new package execution required.'},'commands':{kind:['python3','tools/edition_release.py','--edition','low-energy',kind,'--package',pid,'--output','.local/low-energy-release-runs/'+pid+'-'+kind+'-RUN'] for kind in ['build','trust']},'source_supplements':copy.deepcopy(oldpkg.get('source_supplements',[]))}
 assert not any(p['id']==pid for p in data['proof_packages']);data['proof_packages'].append(package)
 paths+=list({r['source_artifact'] for r in read(BASE/'existing-input-resource-bindings.json')['resources']});paths.append(artifact['source'])
 artifact_index={r['path']:r for r in exported['artifacts']};stored_artifacts={(r.get('path') or r.get('target')):r for r in state['artifacts']}
 for resource in read(BASE/'existing-input-resource-bindings.json')['resources']:
  for table in [artifact_index,stored_artifacts]:
   row=table[resource['target_artifact']]
   if ref not in row['source_revisions']:row['source_revisions'].append(ref)
 data['runtime_views'][pid]={'source_commit':ref,'paths':sorted(set(paths)),'resource_bundles':[],'selection_status':'mapped','pending_source_paths':[],'ambiguous_source_paths':[],'pending_bindings':[],'commands':['python3','tools/edition_materials.py','--edition','low-energy','--view',pid,'--output','.local/low-energy-views/'+pid+'-RUN']}
 observed=read(BASE.parent/'publish-current-selection-review-62da11e0.json')
 for o in observed['observations']:
  if o['path'].startswith('papers/'):
   paper=o['path'].split('/')[1];data['selection_identity'][paper]['sha256']=o['current_sha256']
 data['generator_identity']['latest_incremental_claim_binding']={'claim':'low1.L23','source_commit':ref,'scope':'Four exact complete fixed-source modules, canonical shim, full-light consumer and original receipt; earlier E055 source retained in Git and export history.'}
 layout=ROOT/'tools/ci_layout.tsv';old_layout=layout.read_bytes();newnames=[r['target'] for r in rows]+[aggregate]
 known={line.split('\t')[1] for line in old_layout.decode().splitlines() if '\t' in line};assert not known.intersection(newnames)
 changes['tools/ci_layout.tsv']=old_layout+''.join('s9-02\t'+n+'\n' for n in sorted(newnames)).encode()
 changes['tools/export-map.json']=like(ep,old_export,exported);changes['docs/low-energy-release-map.json']=like(mp,old_map,data)
 state['selected_entries'].append(pid)
 state['entries'][pid]={'paper':'low-energy-phenomenology','ref':ref,'modules':sum(not stored[m].get('source_module','').startswith('file:') for m in members),'files':sum(stored[m].get('source_module','').startswith('file:') for m in members)+4}
 private_changes={sp:like(sp,old_state,state)}
 metadata_dir=ROOT/'.local/second-edition-20261009'
 catalog_path=metadata_dir/'catalog-all.json';catalog=read(catalog_path);old_catalog=copy.deepcopy(catalog)
 entry={'id':pid,'paper':'low-energy-phenomenology','ref':ref,'roots':[],'files':[{'source':r['source_path'],'target':r['target'],'ref':ref} for r in rows],'artifacts':[{'source':artifact['source'],'target':artifact['path'],'ref':ref,'role':'evidence'}]}
 assert not any(e['id']==pid for e in catalog['entries']);catalog['entries'].append(entry)
 catalog['entry_file_target_overrides'][pid]={public[m]['source_path']:m for m in members+[r['target'] for r in rows]}
 private_changes[catalog_path]=like(catalog_path,old_catalog,catalog)
 for filename in ['low-energy-claim-metadata.json','closures-all.json']:
  path=metadata_dir/filename;value=read(path);before=copy.deepcopy(value)
  if filename.startswith('low-energy-claim'):
   value['package_claims']['low-energy-l21-l23-e055']['claims'].remove('low1.L23')
   value['package_claims'][pid]={'claims':['low1.L23'],'revision':ref,'original_producer_roots':[e['source_path'] for e in claim['producers']],'direct_consumer_roots':[e['source_path'] for e in claim['direct_consumers']],'material_counts':{'lean_file_targets':4,'main_roots':0,'new_artifacts':1},'historical_evidence_scope':'Fixed C62 original unit repair and certified producer; complete E055 input closure retained with verified identical C62 source/import/resource identity.'}
  else:value[pid]={'ref':ref,'modules':[],'files':sorted(set(paths)-{artifact['source']})}
  private_changes[path]=like(path,before,value)
 override_path=metadata_dir/'low-energy-map-package-overrides.json';overrides=read(override_path);before=copy.deepcopy(overrides)
 overrides[pid]={'claim_ids':['low1.L23'],'source_commit':ref,'lean_target':aggregate,'required_imports':['H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePreparedThomsonMatchingBridge','H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedThomsonFullLightReturn'],'reason':'Final L23 uses the fixed raw-unit owner and its complete full-light consumer. The prior E055 source and independently paid consumer environment remain recorded.'}
 private_changes[override_path]=like(override_path,before,overrides)
 report={'schema':'h0mework/L23-fixed-source-material-application@1','mode':'apply' if args.apply else 'dry-run','ok':True,'head_before':head,'source_commit':ref,'source_upper_bound_unchanged':True,'new_complete_modules':4,'original_declaration_roots':13,'existing_inputs':len(members),'existing_input_epoch_aliases_added':len(added_epochs),'embedded_resources_verified':23,'new_original_receipt_sha256':artifact['source_sha256'],'new_package':package,'tracked_changed_files':sorted(changes),'existing_public_module_bytes_unchanged':True,'existing_CI_placements_unchanged':len(known),'new_CI_module_placements':{n:'s9-02' for n in sorted(newnames)},'original_E055_source_and_receipt_retained':True,'formal_kernel_acceptance':False}
 if args.apply:
  for path,raw in changes.items():atomic(ROOT/path,raw)
  for path,raw in private_changes.items():atomic(path,raw)
  for row in rows:assert sv.module_views(row,public)[1]==(BASE/'source'/row['source_path']).read_bytes()
 (BASE/('applied.json' if args.apply else 'application-dry-run.json')).write_bytes(encoded(report,2,False))
 print(json.dumps({k:report[k] for k in ['mode','ok','new_complete_modules','original_declaration_roots','existing_input_epoch_aliases_added','existing_CI_placements_unchanged']}))
if __name__=='__main__':main()
