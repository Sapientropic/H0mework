from pathlib import Path
import argparse,copy,importlib.util,json,os,stat,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[3];BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
sp=importlib.util.spec_from_file_location('tuple_source_view',BASE/'source_view-candidate.py');sv=importlib.util.module_from_spec(sp);sp.loader.exec_module(sv);sv.ROOT=ROOT
read=lambda p:json.loads(p.read_bytes())
write=lambda p,d:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')


def atomic_bytes(path,data):
 mode=stat.S_IMODE(path.stat().st_mode)
 with tempfile.NamedTemporaryFile(dir=path.parent,prefix='.'+path.name+'.',delete=False) as stream:
  temporary=Path(stream.name)
  os.fchmod(stream.fileno(),mode)
  stream.write(data)
 try:os.replace(temporary,path)
 finally:temporary.unlink(missing_ok=True)


def json_like(path,before,after):
 raw=path.read_bytes()
 for indent in (1,2,4):
  for sorted_keys in (False,True):
   options={'ensure_ascii':False,'indent':indent,'sort_keys':sorted_keys}
   if (json.dumps(before,**options)+'\n').encode()==raw:
    return (json.dumps(after,**options)+'\n').encode()
 raise AssertionError('Existing JSON layout is not one of the repository formats: '+str(path))


def main():
 parser=argparse.ArgumentParser(description='Root-owned exact six paired private-owner bindings and source-view adapter')
 parser.add_argument('--apply',action='store_true');args=parser.parse_args()
 plan_path=BASE/'plan.json';plan=read(plan_path)
 assert sv.sha(plan_path.read_bytes())=='fc59640dd472a3a84f66cf48475124ffdffc665c9d74ecff9d46298788313332'
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();assert head==plan['head']
 assert not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT)
 marker_path=ROOT/'.local/acceptance-execution-20261010/cohort-freeze.json';marker=read(marker_path)
 assert marker['head']==head and marker['official_dispatch_hold'] is True
 assert all(sv.sha((ROOT/p).read_bytes())==digest for p,digest in marker['files'].items())
 for prefix in ('tool','test'):
  assert sv.sha((ROOT/plan[prefix+'_base_path']).read_bytes())==plan[prefix+'_base_sha256']
  assert sv.sha((ROOT/plan[prefix+'_candidate_path']).read_bytes())==plan[prefix+'_candidate_sha256']
 tests=read(ROOT/plan['unit_tests_path']);assert tests['ok'] and tests['tests']==70 and tests['errors']==tests['failures']==0
 focused=read(ROOT/plan['focused_verification_path']);assert focused['ok'] and focused['inputs_unchanged'] and len(focused['steps'])==3
 assert all(s['exit_code']==0 for s in focused['steps'])
 impact=read(ROOT/plan['actual_scope_membership_path']);assert sv.sha((ROOT/plan['actual_scope_membership_path']).read_bytes())==plan['actual_scope_membership_sha256']
 assert impact['controls_unchanged'] and impact['prior_counts_match_all_51']
 assert impact['current_passed_count']==32 and impact['current_passed_intersections']==[]
 assert impact['old42_recursive_modules']==25259 and impact['old42_candidate_intersections']==[]
 assert impact['original_native_scope_intersections'][0]['modules']==18238 and impact['original_native_scope_intersections'][0]['candidate_paths']==[]
 ex_path=ROOT/'tools/export-map.json';assert sv.sha(ex_path.read_bytes())==plan['export_map_sha256']
 exported=read(ex_path);before_export=copy.deepcopy(exported);rows={r['path']:r for r in exported['modules']};assert len(rows)==len(exported['modules'])
 inverse={r['target']:r for r in exported['modules']}
 state_path=ROOT/'.local/migration/state2.json';state=read(state_path);before_state=copy.deepcopy(state)
 stored={}
 for collection in ('files','explicit_files'):
  for row in state[collection]:
   assert row['path'] not in stored
   stored[row['path']]=row
 changes={};views={};summaries=[]
 with tempfile.TemporaryDirectory(prefix='apply-inverse-',dir=BASE) as directory:
  shadow=Path(directory)
  for item in plan['rows']:
   row=rows[item['path']];private=stored[item['path']]
   for key in ('path','target','source_path','source_revision','source_sha256','source_revisions'):assert row[key]==item[key]
   assert private['target_module']==row['target'] and private['source_sha256']==row['source_sha256']
   before=(ROOT/row['path']).read_bytes();assert sv.sha(before)==item['before_target_sha256']==row['target_sha256']==private['transformed_sha256']
   assert not row.get('private_owner_string_rewrites') and not private.get('private_owner_string_rewrites')
   prior=sv.module_views(row,inverse);candidate=(ROOT/item['candidate_path']).read_bytes()
   assert sv.sha(candidate)==item['after_target_sha256']
   assert sv.rewrite_private_owner_strings(before.decode(),item['private_owner_string_rewrites']).encode()==candidate
   assert sv.rewrite_private_owner_strings(candidate.decode(),item['private_owner_string_rewrites'],reverse=True).encode()==before
   old_row=copy.deepcopy(row);old_private=copy.deepcopy(private)
   row['private_owner_string_rewrites']=copy.deepcopy(item['private_owner_string_rewrites'])
   private['private_owner_string_rewrites']=copy.deepcopy(item['private_owner_string_rewrites'])
   row['target_sha256']=private['transformed_sha256']=sv.sha(candidate)
   for new,old in ((row,old_row),(private,old_private)):
    omitted={'private_owner_string_rewrites','target_sha256','transformed_sha256'}
    assert {k:v for k,v in new.items() if k not in omitted}=={k:v for k,v in old.items() if k not in omitted}
   target=shadow/row['path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(candidate)
   sv.ROOT=shadow
   try:assert sv.module_views(row,inverse)==prior
   finally:sv.ROOT=ROOT
   changes[row['path']]=candidate;views[row['path']]=prior;summaries.append(item)
 paths=set(changes);assert len(paths)==6
 assert sum(len(item['private_owner_string_rewrites']) for item in plan['rows'])==12
 assert all(new==old for new,old in zip(exported['modules'],before_export['modules']) if new['path'] not in paths)
 assert {k:v for k,v in exported.items() if k!='modules'}=={k:v for k,v in before_export.items() if k!='modules'}
 assert {k:v for k,v in state.items() if k not in ('files','explicit_files')}=={k:v for k,v in before_state.items() if k not in ('files','explicit_files')}
 for collection in ('files','explicit_files'):
  assert all(new==old for new,old in zip(state[collection],before_state[collection]) if new['path'] not in paths)
 map_changes={};references={}
 for name in ('docs/first-release-map.json','docs/second-edition-map.json','docs/low-energy-release-map.json'):
  data=read(ROOT/name);old_map=copy.deepcopy(data);hits=[]
  def visit(value):
   if isinstance(value,dict):
    public=value.get('public')
    if isinstance(public,dict) and public.get('path') in paths:
     path=public['path'];assert public['sha256']==next(i['before_target_sha256'] for i in plan['rows'] if i['path']==path)
     public['sha256']=rows[path]['target_sha256'];hits.append(path)
    for child in value.values():visit(child)
   elif isinstance(value,list):
    for child in value:visit(child)
  visit(data);references[name]=hits
  if hits:map_changes[name]=json_like(ROOT/name,old_map,data)
 assert references['docs/first-release-map.json']==[]
 first_sha=sv.sha((ROOT/'docs/first-release-map.json').read_bytes())
 assert first_sha=='70a109c44e4fa0907f817e5ff7751029562415d82b0a1b48cb854053aeba78be'
 live=subprocess.check_output(['ps','-axo','pid=,command='],text=True)
 for path in paths:assert not any('/bin/lean ' in line and str(ROOT/path) in line for line in live.splitlines())
 charged_path=ROOT/'.local/physics-acceptance-20261010/new9-charged-transfer-build-72d341e7-provenance/before.json'
 charged=read(charged_path);charged_scope=charged['package_inputs']['v2-9c73-charged-transfer'];assert len(charged_scope['files'])==3191 and not(paths&set(charged_scope['files']))
 assert all(sv.sha((ROOT/p).read_bytes())==digest for p,digest in marker['files'].items())
 assert not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT)
 export_bytes=json_like(ex_path,before_export,exported)
 state_bytes=json_like(state_path,before_state,state)
 tracked=sorted([*paths,'tools/source_view.py','tools/test_publication.py','tools/export-map.json',*map_changes])
 report={'schema':'h0mework/private-joint-price-owner-application@1','mode':'apply' if args.apply else 'dry-run','ok':True,
         'head_before':head,'plan_sha256':sv.sha(plan_path.read_bytes()),'source_changes':summaries,'tracked_changed_files':tracked,
         'private_changed_files':['.local/migration/state2.json'],'direct_map_references':references,'exact_public_and_original_inverse':True,
         'imports_options_definitions_types_and_math_unchanged':True,'all_other_export_state_records_unchanged':True,
         'registered32_and_old42_and_runtime_source_intersections':[],'charged_source_scope_sha256':charged_scope['digest'],
         'charged_source_intersection':[],'tool_in_charged_global_snapshot':True,'live_source_intersections':[],
         'formal_kernel_acceptance':False,'first_release_map_sha256':first_sha}
 if args.apply:
  for path,candidate in changes.items():atomic_bytes(ROOT/path,candidate)
  for prefix in ('tool','test'):atomic_bytes(ROOT/plan[prefix+'_base_path'],(ROOT/plan[prefix+'_candidate_path']).read_bytes())
  atomic_bytes(ex_path,export_bytes)
  atomic_bytes(state_path,state_bytes)
  for name,data in map_changes.items():atomic_bytes(ROOT/name,data)
  for path in paths:assert sv.module_views(rows[path],inverse)==views[path]
  assert sv.sha((ROOT/'docs/first-release-map.json').read_bytes())==first_sha
 out=BASE/('applied.json' if args.apply else 'application-dry-run.json');write(out,report)
 print(json.dumps({'mode':report['mode'],'ok':True,'source_files':6,'rules':12,'tracked_files':len(tracked),'direct_map_refs':{k:len(v) for k,v in references.items()}}))

if __name__=='__main__':main()
