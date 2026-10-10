from pathlib import Path
import importlib.util,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[3];BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
sp=importlib.util.spec_from_file_location('private_source_view',BASE/'source_view-candidate.py');sv=importlib.util.module_from_spec(sp);sp.loader.exec_module(sv)
sv.ROOT=ROOT
sha=lambda raw:hashlib.sha256(raw).hexdigest()
write=lambda p,d:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
ex_raw=(ROOT/'tools/export-map.json').read_bytes();ex=json.loads(ex_raw);inverse={r['target']:r for r in ex['modules']}
rows=[r for r in ex['modules'] if r['path'].endswith('/SourceMasterCorrectionJointPrice.lean')];assert len(rows)==6
result=json.loads((BASE/'environment-verification-72d341e7/result.json').read_bytes());assert result['ok'] and result['inputs_unchanged']
case_rows=[];candidate_root=BASE/'candidate-root';historical=[]
for row in rows:
 raw=(ROOT/row['path']).read_bytes();assert sha(raw)==row['target_sha256'];assert row['source_sha256']=='ffe4fe9efc08edfe7493f4dcace742739bb6e37e661694474af004d0aa29dde2'
 old_view,original=sv.module_views(row,inverse)
 prefix=row['target'].rsplit('.',1)[0]+'.'
 rules=[];providers=[]
 for stem,decl,expectedsha in (
  ('SourceJointRadialSpatialReturn','spatial_positive','fc3b2c8e66ea8dbd70b2fc06c6b85b06338bcd0703b9a402cacaebbf0077087c'),
  ('SourceJointRadialPrice','physical_price_shape','4dab34dea4e58ac58b593b85b5ec2b6126d75e9f631fa57f4a60cc2f5ae49cb3')):
  provider=inverse[prefix+stem];assert provider['source_sha256']==expectedsha
  assert provider['source_revision']==row['source_revision']
  providers.append({'declaration':'LowEnergy.PreparationPhysicalJointRadialForcing.'+decl,
                    'module':provider['target'],'path':provider['path'],'source_path':provider['source_path'],
                    'source_revision':provider['source_revision'],'source_sha256':provider['source_sha256'],
                    'target_sha256':provider['target_sha256']})
  rules.append({'source_owner':'_private.'+stem,'target_owner':'_private.'+provider['target']})
 assert not row.get('private_owner_string_rewrites')
 transformed=sv.rewrite_private_owner_strings(raw.decode(),rules).encode()
 assert sv.rewrite_private_owner_strings(transformed.decode(),rules,reverse=True).encode()==raw
 assert sv.import_tokens(raw.decode())==sv.import_tokens(transformed.decode())
 p=candidate_root/row['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(transformed)
 newrow={**row,'target_sha256':sha(transformed),'private_owner_string_rewrites':rules}
 sv.ROOT=candidate_root;newview,neworiginal=sv.module_views(newrow,inverse);sv.ROOT=ROOT
 assert neworiginal==original and newview==old_view
 if '/R9c73a630/' in row['path']:assert sha(transformed)==result['candidate_public_sha256']
 code=original.decode();start=code.index('open Lean Elab Term in\nelab "paidCorrectionGeometry% ')
 end=code.index('\nprivate theorem side_scaled',start)
 math=code[:start]+code[end:]
 obj=subprocess.run(['git','-C','runtime/original-source-repository','show',row['source_revision']+':'+row['source_path']],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 historical.append({'revision':row['source_revision'],'path':row['source_path'],'git_object_present':obj.returncode==0,
                    'git_source_sha256':sha(obj.stdout) if obj.returncode==0 else None,
                    'same_as_original_source':obj.returncode==0 and obj.stdout==original,
                    'original_source_sha256':sha(original),'error':obj.stderr.decode().strip() if obj.returncode else None})
 if obj.returncode==0:assert obj.stdout==original
 case_rows.append({'path':row['path'],'target':row['target'],'source_path':row['source_path'],'source_revision':row['source_revision'],
                   'source_revisions':row.get('source_revisions'),'source_sha256':row['source_sha256'],
                   'original_source_sha256_verified':sha(original),'source_origin':row.get('source_origin'),
                   'before_target_sha256':sha(raw),'after_target_sha256':sha(transformed),'candidate_path':p.relative_to(ROOT).as_posix(),
                   'private_owner_string_rewrites':rules,'producer_bindings':providers,'full_inverse_public_bytes_exact':True,
                   'full_inverse_original_bytes_exact':True,'types_definitions_and_math_body_sha256':sha(math.encode()),
                   'source_options':[line for line in code.splitlines() if line.startswith('set_option ')],
                   'imports_unchanged':True,'math_changed':False})
assert len({r['types_definitions_and_math_body_sha256'] for r in case_rows})==1
impact_path=ROOT/'.local/acceptance-execution-20261010/joint-price-membership-72d341e7/result.json'
impact=json.loads(impact_path.read_bytes())
assert impact['controls_unchanged'] and impact['prior_counts_match_all_51']
assert impact['current_passed_count']==32 and impact['current_passed_intersections']==[]
assert impact['old42_recursive_modules']==25259 and impact['old42_candidate_intersections']==[]
assert {r['path'] for r in impact['candidate_sources']}=={r['path'] for r in rows}
plan={'schema':'h0mework/private-joint-price-owner-plan@1','head':'72d341e7964e6ba09755edf9601805e75b38ff56',
      'scope':'Two registered tuple owner strings only; declarations/types/definitions/math and all compiler options unchanged.',
      'public_applied':False,'rows':case_rows,'source_count':6,'rule_count':12,
      'tool_base_path':'tools/source_view.py','tool_base_sha256':sha((ROOT/'tools/source_view.py').read_bytes()),
      'tool_candidate_path':(BASE/'source_view-candidate.py').relative_to(ROOT).as_posix(),'tool_candidate_sha256':sha((BASE/'source_view-candidate.py').read_bytes()),
      'test_base_path':'tools/test_publication.py','test_base_sha256':sha((ROOT/'tools/test_publication.py').read_bytes()),
      'test_candidate_path':(BASE/'test_publication-candidate.py').relative_to(ROOT).as_posix(),'test_candidate_sha256':sha((BASE/'test_publication-candidate.py').read_bytes()),
      'export_map_sha256':sha(ex_raw),'original_git_source_checks':historical,
      'unit_tests_path':(BASE/'unit-tests.json').relative_to(ROOT).as_posix(),'unit_tests_sha256':sha((BASE/'unit-tests.json').read_bytes()),
      'focused_verification_path':(BASE/'environment-verification-72d341e7/result.json').relative_to(ROOT).as_posix(),
      'focused_verification_sha256':sha((BASE/'environment-verification-72d341e7/result.json').read_bytes()),
      'actual_scope_membership_path':impact_path.relative_to(ROOT).as_posix(),'actual_scope_membership_sha256':sha(impact_path.read_bytes()),
      'repo_wide_pattern_search':'Root actual Versions-wide pure tuple / let owner search found only these 6 copies / 12 owner literals.',
      'ci_cache_basis':'Existing actual51 membership: 32 passed, old42 25259 sources and runtime18238 are disjoint; source_view.py not in CI compatibility fields. An actual planner comparison is still required in Root window.'}
write(BASE/'plan.json',plan)
print(json.dumps({'plan':str((BASE/'plan.json').resolve()),'sha256':sha((BASE/'plan.json').read_bytes()),'sources':6,'rules':12,
                  'inverse':True,'math_identity':True,'git_sources_present':sum(h['git_object_present'] for h in historical)}))
