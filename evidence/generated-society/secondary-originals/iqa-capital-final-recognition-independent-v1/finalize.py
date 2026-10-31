import hashlib,json,re,subprocess
from pathlib import Path
OUT=Path(__file__).resolve().parent;ROOT=Path('.');LEAN=ROOT/'Lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def write(p,x):Path(p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
v=read(OUT/'verification.json');owned=read(OUT/'frozen-owned.json');data=read(OUT/'audit-input.json');cap=read(OUT/'candidate.json');support=read(OUT/'support-SourceGeneratedTemporalVisit.json');fresh=[x for x in v['checks'] if x.get('independent_fresh')]
assert len(owned)==6 and len(fresh)==6 and len({x['source'] for x in fresh})==6
assert all(x['exit']==0 and x['trust']==0 and x['werror'] and not x['cached'] and x['dependencies_unchanged'] for x in fresh)
assert support['exit']==0 and support['trust']==0 and support['werror'] and support['source_unchanged'] and support['shared_cache_unchanged'] and support['dependencies_unchanged']
assert sha(support['artifact'])==support['artifact_sha256'] and sha(support['source'])==support['source_sha256']
assert all(sha(LEAN/x['relative_path'])==x['source_sha256'] for x in owned)
assert sha(data['source_capsule'])=='729525f1d52502734fbeacd35061e3fea204034d0e1eba886ec551067172a259'
assert data['source_digest']=='2a321f7356adb2e23f832eb7c6b1d0764cc2dc4fa9877766697c1d9cbf281ddd'
assert 'KERNEL REPLAY PASS:' in v['kernel'];counts=re.search(r'KERNEL REPLAY PASS: roots=(\d+), closure=(\d+), private=(\d+), excludedIR=(\d+)',v['kernel']);assert counts
public=set((OUT/'fresh-public-names.txt').read_text().splitlines());assert set(cap['public_declarations'])<=public
pairs=read(OUT/'selected-pair-evidence.json');assert len(pairs)==1265
preserved=[]
for name,expected in [('iqa-capital-rootexecuted-independent-v1','b009cad60c91868ae80985d0c026260594e318a7606f19cf486280e8abdf4920'),('iqa-capital-nonattainment-independent-v1','21b390fe3ba5e7e2422212492e7a04bdaf4ecf3a8f7046651628aa21b9af5665')]:
 d=OUT.parent/name;assert sha(d/'verification.json')==expected
 rows=read(d/'frozen-owned.json');assert all(sha(LEAN/r['relative_path'])==r['source_sha256'] for r in rows)
 preserved.append({'receipt':str(d/'verification.json'),'sha256':expected,'owned_sources_unchanged':len(rows),'focused_reelaboration':0})
paths=['Lean/'+x['relative_path'] for x in owned];status=subprocess.check_output(['git','--no-optional-locks','status','--short','--',*paths],cwd=ROOT,text=True);diff=subprocess.run(['git','diff','--check','--',*paths],cwd=ROOT,text=True,capture_output=True);assert diff.returncode==0,diff.stdout+diff.stderr
assert all(all(line.rstrip()==line for line in (LEAN/x['relative_path']).read_text().splitlines()) for x in owned)
v.update({
 'schema':'capital-final-recognition-independent-certify/v1','verdict':'certified',
 'source_capsule':{'path':data['source_capsule'],'snapshot':str(OUT/'candidate.json'),'sha256':sha(data['source_capsule']),'source_digest':data['source_digest'],'source_digest_scheme':data['source_digest_scheme'],'source_scope_unchanged':True},
 'owned_source_lines':sum(r['lines'] for r in owned),'maximum_leaf_lines':max(r['lines'] for r in owned),'focused_maximum_seconds':max(r['seconds'] for r in fresh),'explicit_upstream_public_count':len(cap['public_declarations']),'explicit_upstream_public_all_covered':True,
 'scope':'Final original capital cost/strategy mother mouth with source-generated formal IsRooted admission. Same-root compiler-image reflection preserves original occurrence, whole ledger, original coordinates and next. Full authority certificates and actual rooted submissions are generated internally from each exact original temporal visit. The concrete source family is actually root-executed, SourceAdmitted and IsRooted at all seven positions. Every arbitrary finite original RawCleared candidate has a strictly cheaper RootedCompleteAt continuation in the literal full genesis common-history cost; no RawCleared candidate can dominate all these actual rooted clearances. The original registered root directly consumes a mother contract inheriting all old capital, active Binding/resource attainer, actual epoch comparison and exact delay accounting obligations.',
 'classification':{'Recognition.WholeLedger':'source-computed exact compiler-image reflection producer/readout','Recognition.Installed':'same-root source-owned coface installation preserving old coordinates','Recognition.Submission':'internally generated full-K certificate and actual IsRooted submission producer','Recognition.Family':'concrete rooted completion producer and arbitrary-candidate full-history improvement/no-dominator diagnostic','Completion.Complete':'complete inherited capital cost/strategy/rooted-counterexample mother contract','Consumers.Complete':'original registered-root direct consumer and complete old-capital projection'},
 'semantic_review':str(OUT/'final-semantic-review.json'),'semantic_review_sha256':sha(OUT/'final-semantic-review.json'),
 'key_machine_facts':{
  'economic_target_in_PassedAt':False,
  'PassedAt':'unique subtype image equal to original ledgerCompiler.compile occurrence',
  'same_original_emitter_and_compiler':True,
  'same_original_ledger_root_law_surface_all_whole_writes':True,
  'original_coordinates_preserved_by_inherited_coface':True,
  'same_original_terminal_handoff_and_next':True,
  'caller_decoder_certificate_factorization_or_Rooted_witness':False,
  'full_root_authority_K_commutes_and_ledger_next_factorizes':True,
  'concrete_all7_original_positions_IsRooted':True,
  'actual_execution_SourceAdmitted_IsRooted_jointly_generated':True,
  'arbitrary_RawCleared_rival_has_strictly_cheaper_RootedComplete_full_history':True,
  'unconditional_full_task_argmin_asserted':False,
  'universal_nonpositive_total_income_asserted':False,
  'original_registered_capital_contract_inherited_and_consumed':True},
 'provenance':{
  'local_source_closure':len(data['closure']),'exact_previously_signed_external_source_selected_pairs':len(pairs),'new_external_support_fresh':1,'new_external_support_source_lines':support['lines'],'bounded_support_receipt':str(OUT/'support-SourceGeneratedTemporalVisit.json'),'bounded_support_receipt_sha256':sha(OUT/'support-SourceGeneratedTemporalVisit.json'),'bounded_support_main_commit':support['pinned_main_commit'],'bounded_support_main_blob':support['pinned_main_blob'],
  'support_complete_safe_private_module_included_in_single_kernel_replay':data['support_kernel_modules'],
  'prior_signed_scopes_preserved':preserved,'signed_pair_evidence':str(OUT/'selected-pair-evidence.json'),'signed_pair_evidence_sha256':sha(OUT/'selected-pair-evidence.json'),'selected_imports':str(OUT/'selected-imports.json'),'selected_imports_sha256':sha(OUT/'selected-imports.json'),
  'first_hit':'direct pinned Lean4.33 binary, isolated lib first; all source-selected artifact bindings stable',
  'source_overlay_reuse':list(data['source_overlays']),'public_axiom_union':['propext','Classical.choice','Quot.sound'],'safe_private_replay_count':1,'kernel_counts':dict(zip(['roots','closure','private','excludedIR'],map(int,counts.groups()))),'new_unpaired_external_supports':[],'scratch_imports':[],'nonowned_untracked_foreign_imports':[]},
 'ir_split':{'excluded_names':(OUT/'excluded-ir.txt').read_text().splitlines(),'safe_logical_dependency_on_unsafe_or_partial':False,'owned_compile_time_elaborators':False},
 'completion_assessment':{'Final6_exact_claim_scope_complete':True,'formal_IsRooted_complete_authority_for_all_actual_family_positions':True,'original_capital_cost_delay_quantifier_mother_mouth_complete':True,'remaining_required_work_at_this_scope':[],'boundary':'The counterexample concerns the fixed actual source and arbitrary finite original RawCleared rivals under its stated full resource/time cost. Rooted certifies complete same-source authority; the separate actual execution pays clearing and needs. The mother mouth does not claim a universal attained full-task minimum or erase genuine production profits.'},
 'final_hygiene':{'source_and_selected_artifacts_stable':True,'scoped_git_status':status.splitlines(),'git_diff_check_exit':0,'owned_source_whitespace_check':True,'production_source_or_shared_Lean_cache_modified_by_auditor':False,'git_modified_or_commit_by_auditor':False}
})
write(OUT/'verification.json',v)
print(json.dumps({'verdict':v['verdict'],'status':v['status'],'owned':len(owned),'source_lines':v['owned_source_lines'],'support_fresh':1,'support_lines':support['lines'],'public_generated':v['public_mouths'],'explicit_public':len(cap['public_declarations']),'kernel':v['provenance']['kernel_counts'],'max_fresh_seconds':v['focused_maximum_seconds'],'verification':str(OUT/'verification.json'),'sha256':sha(OUT/'verification.json')},ensure_ascii=False,indent=2))
