from pathlib import Path
import hashlib,json,subprocess,sys,copy
ROOT=Path(__file__).resolve().parents[3];BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
import source_view as sv
sha=lambda b:hashlib.sha256(b).hexdigest()
write=lambda p,d:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
old=BASE/'environment-verification-source72d341e7';focused=json.loads((old/'result.json').read_bytes());consumer=BASE/'independent-consumer-corrected-source72d341e7/result.json';c=json.loads(consumer.read_bytes())
assert focused['inputs_unchanged'] and focused['steps'][0]['exit_code']==focused['steps'][1]['exit_code']==0 and c['ok'] and c['inputs_unchanged']
exraw=(ROOT/'tools/export-map.json').read_bytes();ex=json.loads(exraw);inverse={r['target']:r for r in ex['modules']}
row=next(r for r in ex['modules'] if r['path']==focused['public_path']);raw=(ROOT/row['path']).read_bytes();assert sha(raw)==row['target_sha256']
rules=focused['private_owner_expression_rewrites'];assert len(rules)==3 and not row.get('private_owner_expression_rewrites')
fullcandidate=sv.rewrite_private_owner_expressions(raw.decode(),rules).encode();assert sha(fullcandidate)==focused['candidate_public_sha256']
assert sv.rewrite_private_owner_expressions(fullcandidate.decode(),rules,reverse=True).encode()==raw
prior=sv.module_views(row,inverse)
shadow=BASE/'candidate-root';p=shadow/row['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(fullcandidate)
newrow={**row,'target_sha256':sha(fullcandidate),'private_owner_expression_rewrites':rules}
sv.ROOT=shadow
try:assert sv.module_views(newrow,inverse)==prior
finally:sv.ROOT=ROOT
assert sv.import_tokens(raw.decode())==sv.import_tokens(fullcandidate.decode())
text=raw.decode();start=text.index('section PaidHelpers');end=text.index('end PaidHelpers',start)+len('end PaidHelpers')
math=text[:start]+text[end:];aftertext=fullcandidate.decode();a=aftertext.index('section PaidHelpers');b=aftertext.index('end PaidHelpers',a)+len('end PaidHelpers');assert aftertext[:a]+aftertext[b:]==math
obj=subprocess.run(['git','-C','runtime/original-source-repository','show',row['source_revision']+':'+row['source_path']],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert obj.returncode==0 and obj.stdout==prior[1]
memberbase=ROOT/'.local/acceptance-execution-20261010/joint-price-membership-72d341e7';summary=json.loads((memberbase/'result.json').read_bytes());members=json.loads((memberbase/'package-module-memberships.json').read_bytes())
packages=summary['packages'];print('PACKAGE_ROW_KEYS',list(packages[0]))
impact=[];passed=[]
for record in packages:
 key=record['map']+':'+record['package'];group=members[key];hits=[row['target']] if row['target'] in group else []
 value={**{k:record.get(k) for k in ('map','package','kernel','modules')},'candidate_modules':hits};impact.append(value)
 if record.get('kernel')=='passed' and hits:passed.append(value)
assert not passed
old42path=ROOT/summary['old42_actual_source_list'];old42=json.loads(old42path.read_bytes());assert row['target'] not in old42 and len(old42)==25259
native=[]
for n in summary['original_native_scope_intersections']:
 info=json.loads((ROOT/n['input_path']).read_bytes())
 files=info['source_scope']['files'] if 'source_scope' in info and 'files' in info['source_scope'] else info.get('sources',info.get('source_files'))
 if files is None:
  print('NATIVE_KEYS',n['run'],list(info));continue
 if isinstance(files,dict):hits=[row['path']] if row['path'] in files or row['target'] in files else []
 else:hits=[row['path']] if row['path'] in files or row['target'] in files else []
 native.append({'run':n['run'],'candidate_paths':hits})
assert all(not n['candidate_paths'] for n in native)
live=subprocess.check_output(['ps','-axo','pid=,command='],text=True);hits=[line for line in live.splitlines() if '/bin/lean ' in line and str(ROOT/row['path']) in line];assert not hits
report={'schema':'h0mework/private-cutoff-time-source-impact@1','formal_acceptance':False,'digest_verification':False,
        'cached_membership_result':(memberbase/'result.json').relative_to(ROOT).as_posix(),'cached_membership_result_sha256':sha((memberbase/'result.json').read_bytes()),
        'package_intersections':impact,'passed_package_intersections':passed,'old42_sources':len(old42),'old42_intersection':[],
        'native_source_intersections':native,'live_compiler_source_intersections':hits,'affected_packages':[r for r in impact if r['candidate_modules']],
        'membership_only_no_rehash_or_kernel_reexecution':True}
write(BASE/'actual-scope-impact.json',report)
plan={'schema':'h0mework/private-cutoff-time-owner-plan@1','public_applied':False,
      'path':row['path'],'target':row['target'],'source_path':row['source_path'],'source_revision':row['source_revision'],'source_revisions':row['source_revisions'],
      'source_sha256':row['source_sha256'],'source_origin':row.get('source_origin'),'before_target_sha256':sha(raw),'after_target_sha256':sha(fullcandidate),
      'candidate_path':p.relative_to(ROOT).as_posix(),'private_owner_expression_rewrites':rules,
      'full_public_inverse_exact':True,'full_original_inverse_sha256':sha(prior[1]),'original_git_bytes_exact':True,
      'math_body_sha256':sha(math.encode()),'imports_unchanged':True,'source_options':[line for line in text.splitlines() if line.startswith('set_option ')],
      'actual_original_provider_rows':focused['producer_rows'],'actual_payer_owner_verification':str((old/'result.json').relative_to(ROOT)),
      'actual_payer_and_full_module_steps':focused['steps'][:2],'original_fixture_false_result_sha256':sha((old/'result.json').read_bytes()),
      'independent_consumer_result':consumer.relative_to(ROOT).as_posix(),'independent_consumer_result_sha256':sha(consumer.read_bytes()),
      'source_impact':(BASE/'actual-scope-impact.json').relative_to(ROOT).as_posix(),'source_impact_sha256':sha((BASE/'actual-scope-impact.json').read_bytes()),
      'existing_source_view_api':'private_owner_expression_rewrites static Name.str literal; no new tool or global option.',
      'export_map_at_observation_sha256':sha(exraw),'head_at_observation':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()}
write(BASE/'plan.json',plan)
print(json.dumps({'plan':str((BASE/'plan.json').resolve()),'sha256':sha((BASE/'plan.json').read_bytes()),'affected_packages':[(x['map'],x['package']) for x in impact if x['candidate_modules']],
                  'passed_intersections':len(passed),'native_intersections':native,'original_git_exact':True}))
