#!/usr/bin/env python3
"""Verify the two-term paid continuation, derived cofiber, and actual original consumers."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

FLAGS = ['--trust=0', '-DElab.async=false', '-DwarningAsError=true', '-DmaxErrors=1',
         '-j1', '-M32000', '-DstderrAsMessages=false']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


_digest_cache = {}
_json_cache = {}


def identity(path):
    stat = Path(path).stat()
    return stat.st_dev,stat.st_ino,stat.st_size,stat.st_mtime_ns


def sha(path):
    key = identity(path)
    if key not in _digest_cache:
        with Path(path).open('rb') as stream:
            _digest_cache[key] = hashlib.file_digest(stream, 'sha256').hexdigest()
    return _digest_cache[key]


def exact(record, root=Path('.')):
    path = root/record['path']
    require(('bytes' not in record or path.stat().st_size==record['bytes']) and sha(path)==record['sha256'],'exact file drift '+str(path))
    return path


def read(path):
    key = identity(path)
    if key not in _json_cache:
        _json_cache[key] = json.loads(Path(path).read_text())
    return _json_cache[key]


def save(path, value):
    with Path(path).open('w') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


_tracked_source_digests = {}


def tracked_source_sha(repo, revision, path):
    relative = path.relative_to(repo).as_posix()
    key = (repo, revision, relative)
    if key not in _tracked_source_digests:
        blob = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
            revision+':'+relative],cwd=repo)
        _tracked_source_digests[key] = hashlib.sha256(blob).hexdigest()
    return _tracked_source_digests[key]


def verify_inherited_kummer_graft(context, prior_context, inputs, prior_inputs, roots, construction):
    graft_path = exact(context['rational_kummer_closure_graft'])
    graft = read(graft_path)
    reuse = construction['graft_reuse']
    audit = exact(reuse['inherited_actual_import_audit'])
    auditor = exact(reuse['audit_source'])
    require(context['rational_kummer_closure_graft']==prior_context['rational_kummer_closure_graft'] and
            sha(graft_path)==inputs['frozen_inputs']['kummer-graft.json']==prior_inputs['frozen_inputs']['kummer-graft.json'] and
            graft['schema']=='rational-kummer-exact-compiled-graft/v1' and
            graft['audit']=={'sha256':sha(audit),'source_sha256':sha(auditor)} and
            len(graft['rows'])==graft['closure_count']==reuse['matched_prior_verified_modules']==29 and
            reuse['old_recompiles']==reuse['library_copies']==0,
            'CP748 inherited verified Kummer graph authority drift')
    for row in graft['rows']:
        selected_object = selected(row['module'],roots)[0]
        require(all(selected_object.samefile(path) for path in (row['first_hit'],row['lake_object'])) and
                sha(selected_object)==row['lake_object_sha256'] and
                sha(row['source'])==row['source_sha256'] and sha(row['trace'])==row['trace_sha256'] and
                Path(row['lake_object']).with_suffix('.olean.hash').read_text().strip()==row['object_lake_hash'],
                'CP748 inherited Kummer source, trace or first-hit drift '+row['module'])


def verify_original_budget_source(repo, row, roots):
    module = row['module']
    manifest_path, verdict_path, signatures_path, production_path, results_path = map(exact, row['bindings'])
    manifest, verdict, signatures, production, results = map(
        read, (manifest_path, verdict_path, signatures_path, production_path, results_path))
    signed_commit = row['tracked_source_commit']
    source = repo/row['main']
    strict = results[module]
    installed, = [item for item in production['production_sources'] if item['module']==module]
    artifact = selected(module,roots)[0]
    require(manifest['checkpoint']=='CP332 candidate native-sigma writeback' and verdict['Verdict']=='certified' and
            set(verdict['axioms'])==AXIOMS and verdict['trust0_warningAsError_asyncFalse'] and
            signatures['files']['manifest.json']==verdict['manifest_sha256']==sha(manifest_path) and
            signatures['files']['verdict.json']==sha(verdict_path) and signatures['production_scope_only'] and
            production['commit']==signed_commit and production['proof_bodies_unchanged'] and
            production['parent_recompiles']==production['copied_library_bytes']==0 and
            exact({'path':production['results'],'sha256':production['results_sha256']})==results_path and
            strict['exit_code']==strict['trust']==0 and strict['warning_as_error'] and not strict['async'] and
            installed['only_module_binding_changes'] and strict['source']==installed['source']==str(source) and
            tracked_source_sha(repo,signed_commit,source)==sha(source)==strict['source_sha256']==
                installed['source_sha256']==row['source_sha256'] and
            all(artifact.samefile(path) for path in (strict['olean'],installed['olean'],exact(row['authority_object']))) and
            sha(artifact)==strict['olean_sha256']==installed['olean_sha256']==row['object_sha256'],
            'CP332 exact signed native writeback budget source drift')


def verify_paid_continuation_parents(repo, package, inputs, stage, context, roots):
    compact = read(exact(inputs['paid_parent_evidence'],package))
    require(compact['schema']=='cofinal-paid-derived-continuation-paid-parent-evidence/v1','CP748 compact parent evidence drift')
    revision = stage['foundation_commit']
    prior = repo/'Verification/no-island/cofinal-paid-history-continuation'
    inherited = compact['inherited_authority']
    evidence = exact(inherited['evidence'],repo)
    require(inherited['rows']==292 and inherited['commit']==revision=='1db039f748f8ca5983035aa78dd18f164ce276db' and
            evidence==prior/'evidence/paid-parents.json','CP747 signed parent evidence drift')
    paths = [prior/name for name in ('manifest.json','certificate.json','inputs.json','certify.py','independent-cost.json','audit-summary.json')]
    for path in (*paths,evidence):
        require(sha(path)==tracked_source_sha(repo,revision,path),'CP747 tracked authority drift '+str(path))
    manifest_path,cert_path,prior_inputs_path,_,cost_path,audit_path = paths
    manifest,cert,prior_inputs,cost,audit = map(read,(manifest_path,cert_path,prior_inputs_path,cost_path,audit_path))
    require(sha(manifest_path)=='56784bf9495031299aab5ab830d52c42d4789a4f3ae150a31ab0bc3d843b0143' and
            sha(cert_path)=='fee5715ace2b56b2d54f8a8cbbed9aa39b8d0a52e10f076848355e12ef1deb4c' and
            manifest['checkpoint']==cert['checkpoint']=='CP747' and cert['verdict']=='certified' and
            set(cert['axioms'])==set(audit['axioms'])==AXIOMS and cert['inputs']['sha256']==sha(prior_inputs_path) and
            cert['paid_parent_evidence']==prior_inputs['paid_parent_evidence'] and exact(cert['paid_parent_evidence'],prior)==evidence and
            cert['independent_cost']['sha256']==sha(cost_path) and cert['audit_summary']['sha256']==sha(audit_path) and
            (cert['counts']['safe'],cert['counts']['private'],cert['counts']['extras'])==(45,28,399) and
            cert['counts']['paid_reused_project_bodies']==292 and cert['counts']['inherited_mathlib_support_bindings']+cert['counts']['new_mathlib_support_bindings']==17 and
            audit['accepted'] and audit['kernel_calls']==cost['kernel_calls']==45 and
            cost['old_ci_replays']==cost['old_source_recompiles']==0 and
            [(r['label'],r['exit_code']) for r in cost['calls'] if r['exit_code']==0]==[('001-gate',0),('002-audit',0)],
            'CP747 signed proof, independent receipt or paid scope drift')
    for path in (*paths[1:],evidence):
        member, = [row for row in manifest['members'] if row['path']==path.relative_to(prior).as_posix()]
        require(exact(member,prior)==path,'CP747 original manifest member drift '+str(path))
    static = cert['default_main_static']
    prior_independent = roots[0].parent.parent/'iqa-cofinal-paid-continuation-independent'
    require(static['verdict']=='exact-inputs-verified' and static['formal_sources'] and static['calls'][-1]['exit_code']==0 and
            static['lean_calls']==static['calls'][-1]['lean_calls']==0 and
            sha(prior_independent/'main-static/provenance.json')==static['sha256'] and
            sha(prior_independent/'main-static.log')==static['calls'][-1]['log_sha256'],
            'CP747 accepted static provenance drift')
    for row in cost['calls']:
        if row['exit_code']==0:
            require(sha(prior_independent/(row['label']+'.receipt.json'))==row['receipt_sha256'] and
                    sha(prior_independent/(row['label']+'.log'))==row['log_sha256'],
                    'CP747 accepted Lean receipt drift '+row['label'])

    require(audit['raw_CIs']==audit['logical_CIs']==audit['kernel_calls']==45 and
            audit['inherited_generated_full_CIs']==audit['compiler_runtime']==audit['inductive_generated_CIs']==[],
            'CP747 independent all-fresh logical scope drift')

    paid_path = exact(stage['paid_parent_bindings'])
    paid = read(paid_path)
    rows = paid['rows']
    require(paid['schema']=='cofinal-paid-derived-paid-parents/v1' and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(rows)==len({row['module'] for row in rows})==296 and rows==context['exact_paid_bodies'] and
            rows[292:]==compact['added_rows'] and compact['selected_lean_path']==paid['selected_lean_path'] and
            paid['old_compilations']==paid['copies']==context['old_objects_copied']==0,
            'CP748 exact paid inventory or aliases drift')
    m,c,promotion_path,prior_stage_path,_ = map(exact,rows[292]['bindings'])
    require(m==manifest_path and c==cert_path and sha(promotion_path)==cert['main_promotion']['sha256'] and
            sha(prior_stage_path)==prior_inputs['frozen_inputs']['stage-map.json']==
                'd5e77e8c7dfcf1fc8c1ab3c5ca437623cb2b62239c55cf9bd5576963e0ecae2c',
            'CP747 exact promoted topology source chain drift')
    prior_stage = read(prior_stage_path)
    prior_context_path = exact(prior_stage['context'])
    prior_context = read(prior_context_path)
    prior_paid_path = exact(prior_stage['paid_parent_bindings'])
    prior_paid = read(prior_paid_path)
    require(sha(prior_context_path)==prior_inputs['frozen_inputs']['context.json'] and
            sha(prior_paid_path)==prior_inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(prior_paid['rows'])==292 and prior_paid['rows']==prior_context['exact_paid_bodies'] and
            prior_paid['old_compilations']==prior_paid['copies']==prior_context['old_objects_copied']==0 and
            context['goldbach_closure_graft']==prior_context['goldbach_closure_graft'] and
            sha(exact(context['goldbach_closure_graft']))==prior_inputs['frozen_inputs']['goldbach-closure-graft.json']==
                inputs['frozen_inputs']['goldbach-closure-graft.json'],
            'CP747 signed parent facts or prior Goldbach graph evidence drift')
    for current,old in zip(rows[:292],prior_paid['rows'],strict=True):
        module = current['module']
        artifact = selected(module,roots)[0]
        require(current=={**old,'object':current['object'],'provider':current['provider']} and
                all(artifact.samefile(p) for p in (current['object'],current['provider'],old['object'],old['provider'])) and
                sha(artifact)==old['object_sha256'] and sha(repo/old['main'])==old['source_sha256'],
                'CP748 inherited CP747 exact binding drift '+module)

    promotion = read(promotion_path)
    require(promotion['exact'] and promotion['old_compilations']==0 and
            promotion['stage_map_sha256']==sha(prior_stage_path) and len(promotion['inputs'])==len(prior_stage['inputs'])==4,
            'CP747 exact promotion scope drift')
    for row,owner,promoted,ending,attempt in zip(rows[292:],prior_stage['inputs'],promotion['inputs'],
            ('Continuation','Payment','Native','TopologyContinuation'),
            ('005','003','002','002'),strict=True):
        module = row['module']
        refs = list(map(exact,row['bindings']))
        strict_path = refs[-1]
        strict = read(strict_path)
        source = repo/row['main']
        artifact = selected(module,roots)[0]
        require(refs[:4]==[manifest_path,cert_path,promotion_path,prior_stage_path] and
                row['binding_kind']=='exact-certified-source-reuse' and row['tracked_source_commit']==revision and
                module.endswith('.'+ending) and module==owner['module']==promoted['module'] and
                row['main']==owner['main']==promoted['main'] and owner['final_attempt']==strict['attempt']==attempt and
                exact(owner['receipt'])==strict_path and promoted['receipt_sha256']==sha(strict_path) and
                strict['source_unchanged'] and strict['exit_code']==strict['old_compilations']==0 and
                set(FLAGS[:3])<=set(strict['command']) and strict['command']==owner['strict_command'] and
                strict['source']==owner['source']==row['source_evidence']['path'] and
                row['source_evidence']['kind']=='retained-source' and
                sha(source)==tracked_source_sha(repo,revision,source)==sha(owner['source'])==sha(strict['source_snapshot'])==
                    owner['source_sha256']==promoted['source_sha256']==strict['source_sha256']==row['source_sha256'] and
                all(artifact.samefile(path) for path in (row['object'],row['provider'],exact(row['authority_object']),
                    exact(owner['object']),exact(strict['object']))) and
                sha(artifact)==row['object_sha256']==promoted['object_sha256'],
                'CP747 exact source, strict compile and selected inode drift '+module)
    verify_inherited_kummer_graft(context,prior_context,inputs,prior_inputs,roots,read(exact(stage['construction_cost'])))
    mathlib = read(exact(context['mathlib_bindings']))['rows']
    require(len(mathlib)==18 and mathlib[:-1]==read(exact(prior_context['mathlib_bindings']))['rows'] and
            all(selected(row['module'],roots)[0].samefile(exact(row['object'])) and exact(row['source']).is_file()
                for row in mathlib[:-1]), 'CP748 exact inherited Mathlib provider drift')
    pin = mathlib[-1]
    mathlib_root = repo/'Lean/.lake/packages/mathlib'
    mathlib_direct = 'Mathlib.Algebra.Homology.Embedding.ExtendHomology'
    mathlib_revision = 'db584cd6d46c92f209a44c0f1c829460d327499d'
    require(pin['module']==mathlib_direct and pin['tracked_source_commit']==mathlib_revision and
            exact(pin['source'])==mathlib_root/Path(*mathlib_direct.split('.')).with_suffix('.lean') and
            tracked_source_sha(mathlib_root,mathlib_revision,exact(pin['source']))==pin['source']['sha256'] and
            selected(mathlib_direct,roots)[0].samefile(exact(pin['object'])) and
            exact(pin['object']).samefile(pin['provider']), 'CP748 exact direct ExtendHomology pin drift')
    require(sum(row['binding_kind']!='exact-certified-source-reuse' for row in rows)==88,
            'CP748 exact legacy parent count drift')
    direct = []
    for ending in ('.Cofinal.Topology.Operations.Closure.Continuation',
            '.Cofinal.Topology.Operations.Closure.Continuation.Native',
            '.RootRelation.PaidSyntaxCompletion','.KernelWrite.NativeSigma.Writeback.Source'):
        row, = [row for row in rows if row['module'].endswith(ending)]
        direct.append(row)
    require(direct[-1]['role']=='CP332 exact original NativeSigma.Writeback.Source',
            'CP748 native budget imported from the wrong provider')
    verify_original_budget_source(repo,direct[-1],roots)
    return paid,[row['module'] for row in direct],mathlib_direct


def selected(module, roots):
    package = module.split('.')[0]
    relative = Path(*module.split('.')).with_suffix('.olean')
    for index, root in enumerate(roots):
        if (root/package).is_dir() or (root/(package+'.olean')).is_file():
            path = root/relative
            require(path.is_file(),'selected package root lacks '+module)
            return path,index
    raise RuntimeError('missing '+module)


def verify_inputs(package, args):
    inputs = read(package/'inputs.json')
    roots = list(map(Path,args.base_lean_path_file.read_text().strip().split(os.pathsep)))
    require(args.compiled_root.resolve()==roots[0].resolve(),'complete compiled root must be first')
    require((args.repo/'Lean/lean-toolchain').read_text().strip()==inputs['lean_toolchain'],'toolchain drift')
    for name,digest in inputs['local_evidence_sha256'].items():
        require(sha(package/name)==digest,'checker/evidence drift '+name)
    base = roots[0].parent
    for name in ('stage-map.json','context.json'):
        require(sha(base/name)==inputs['frozen_inputs'][name],'frozen input drift '+name)
    require(sha(args.base_lean_path_file)==inputs['frozen_inputs']['lean-path.txt'],'compiled view drift')
    stage,context = read(base/'stage-map.json'),read(base/'context.json')
    require(stage['frozen'] and stage['foundation_commit']==inputs['foundation_commit'],
            'frozen foundation drift')
    for key, filename in (('raw_ci_inventory','raw-inventory.json'),('construction_cost','construction-cost.json'),
                          ('paid_parent_bindings','paid-parent-bindings.json'),('context','context.json'),
                          ('compiler_companions','compiler-companions.json'),('output_location','output-location.json'),
                          ('raw_inventory_receipt','receipts/RawInventory-001.receipt.json')):
        require(stage[key]['sha256']==inputs['frozen_inputs'][filename] and exact(stage[key]).samefile(base/filename),'frozen stage binding drift '+filename)
    frozen = {r['module']:r for r in stage['inputs']}
    science = {r['module']:r for r in inputs['science']}
    strict = {r['module']:r for r in read(package/'evidence/science-compiles.json')['rows']}
    require(len(science)==4 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'Retraction','Cochain','Derived','PaidDerivedContinuation'} and
                row['intended_formal_path']=='Lean/'+module.replace('.','/')+'.lean' and
                imports==row['base'] and not any(name.startswith('scratch.') for name in imports),
                'production source import drift '+module)
        receipt = strict[module]
        actual_receipt = read(exact(frozen[module]['receipt']))
        require(receipt['receipt_sha256']==row['strict_receipt_sha256']==frozen[module]['receipt']['sha256'] and
                receipt['source_sha256']==row['source_sha256'] and receipt['object_sha256']==row['artifact_sha256'] and
                receipt['exit_code']==actual_receipt['exit_code']==0 and
                receipt['trust']==0 and receipt['werror'] and not receipt['elab_async'] and
                actual_receipt['source_sha256']==row['source_sha256'] and
                actual_receipt['object']['sha256']==row['artifact_sha256'] and actual_receipt['source_unchanged'] and
                artifact.samefile(exact(actual_receipt['object'])) and
                actual_receipt['command']==frozen[module]['strict_command'] and
                sha(actual_receipt['source_snapshot'])==row['source_sha256'] and
                set(FLAGS[:3]) <= set(actual_receipt['command']) and actual_receipt['old_compilations']==0,
                'strict source/body receipt drift '+module)
        science_actual.append({**row,'selected_olean':str(artifact),'search_path_index':index})

    require(inputs['paid_parent_evidence']['path']=='evidence/paid-parents.json', 'parent evidence member drift')
    paid,direct,mathlib_direct=verify_paid_continuation_parents(args.repo,package,inputs,stage,context,roots)
    imports={m for row in science.values() for m in row['base']} - science.keys()
    require(imports==set(inputs['audit_base']),'CP748 exact direct import scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    parent_view=base.parent/'iqa-cofinal-paid-continuation/lean-path.txt'
    parent_roots=list(map(Path,parent_view.read_text().strip().split(os.pathsep)))
    require(Path(output['logical'])==base and output['payloads']==['objects','receipts','source-root'] and
            output['archive_volume']=='Extension2' and len(roots)==31 and roots==[base/'lib',*parent_roots[1:]] and
            physical.is_relative_to('runtime/ and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','receipts','source-root')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' and
                Path(row['source']).resolve()==physical/'source-root/main'/Path(*row['module'].split('.')).with_suffix('.lean') and
                [arg for arg in row['strict_command'] if arg.startswith('--root=')]==
                    [f"--root={base/'source-root/main'}"] for row in frozen.values()),
            'second SSD output binding drift')
    mathlib = exact(context['mathlib_bindings'])
    require(mathlib.samefile(base/'mathlib-bindings.json') and sha(mathlib)==inputs['frozen_inputs']['mathlib-bindings.json'],
        'frozen Mathlib provider list drift')
    require(imports==set(direct)|{mathlib_direct},'CP748 exact production import drift')
    gate_imports=re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)
    fixed_target, = [row['module'] for row in paid['rows'] if row['role']=='CP747 exact TopologyContinuation']
    division, = [row['module'] for row in paid['rows']
                 if row['module'].endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction')]
    require(gate_imports==[inputs['entry'],fixed_target,division] and not ({division,fixed_target} & imports),
            'CP748 independent fixed-target and original Division Gate-only import drift')
    profile = read(exact(stage['construction_cost']))['kernel_conversion_profile']
    sample = exact(profile)
    record = read(exact(profile['record']))
    require(sample.name=='Retraction-002.sample.txt.zst' and
            profile['first_reported_single_conversion_seconds']==81.6 and profile['final_typechecking_seconds']==8.9 and
            profile['actual_serialization_before_seconds']==19.2 and profile['actual_serialization_after_milliseconds']==40.8 and
            profile['uncompressed_bytes']==602482 and
            profile['uncompressed_sha256']=='b462a513b4d2850a48bef9346c898dca5302f1d15e9505269d617a7846f0baeb' and
            record=={key:value for key,value in profile.items() if key!='record'},
            'CP748 bound original kernel conversion and serialization diagnosis drift')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='cofinal-paid-derived-compiler-companions/v1' and
            companions['companions']==inputs['compiler_companions']==[],
            'CP748 unexpected compiler runtime companion scope')
    require(exact(context['lean_path_compaction'])==exact(inputs['lean_path_compaction']) and
            context['lean_path_compaction']==read(exact(read(parent_view.parent/'stage-map.json')['context']))['lean_path_compaction'],
            'independently checked inherited path compaction drift')
    return inputs,roots,science_actual


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['label']==inputs['audit_label'] and stage['duplicates'] == 0 and
            stage['inherited'] == counts['inherited'] == report['inherited_generated_full_CI_matches'] and
            stage['fresh_replayed'] == counts['safe'] == report['fresh_safe_replayed_CIs'] and
            stage['fresh_replayed']+stage['inherited']+len(stage['compiler_runtime'])==stage['raw']==counts['raw'] and
            not stage['base_has_unverified_sources'] and
            report['fresh_raw_regions'] == 4 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    expected_runtime = [{'name':r['name'],'owner':r['module'],'safe_source':r['owner'],
        'isUnsafe':False,'isPartial':True,'self_edges':1,'nonself_incoming_edges':0,
        'type_preserved':True,'value_preserved':True} for r in inputs['compiler_companions']]
    require(len(expected_runtime)==counts['compiler_runtime']==0 and
            sorted(expected_runtime,key=lambda r:r['name'])==sorted(stage['compiler_runtime'],key=lambda r:r['name']),
            'exact compiler companion CI or logical separation drift')
    require(counts['raw_private']==counts['private']==92, 'private logical scope drift')
    owners = {r['module']:r for r in actual}
    for owner in stage['modules']:
        selected_owner = owners.pop(owner['module'])
        require(sha(owner['selected_olean']) == selected_owner['artifact_sha256'] and
                owner['raw'] == selected_owner['raw_CIs'] and owner['imports'] == selected_owner['raw_imports'] and
                owner['compiler_extras'] == selected_owner['compiler_extras'] and
                hashlib.sha256(json.dumps(owner['compiler_extra_names'],ensure_ascii=False,separators=(',',':')).encode()).hexdigest() ==
                    selected_owner['compiler_extra_names_sha256'],
                'wrong audited owner '+owner['module'])
    require([r['name'] for r in stage['inherited_generated_full_CIs']]==inputs['inherited_generated_CIs'] and
            all(r['same_full_constant_info'] and not r['kernel_replayed']
                for r in stage['inherited_generated_full_CIs']), 'inherited CI qualification drift')
    require(not owners and report['safe_private_original_CIs'] == stage['safe_private'] == counts['safe'] and
            stage['kernel_calls'] == counts['kernel_calls'] and stage['compiler_extras'] == counts['extras'] and
            sum(r['name'].startswith('_private.') for r in stage['declarations']) == counts['private'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['source_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source provenance')
    trace_context = ['S','Root','NextRoot','V','X','_','s','old','before','middle','after',
        'root','prior','nextRoot','next']
    native_context = ['N','V','old','origin','S','Value','Var','_','sort','reader','runtime']
    actual_context = ['observation','nontrivial','half','depth','ordinal']
    public = {
        'continuationRelationBack': (trace_context,0),
        'continuationGeneratorBack': (trace_context,0),
        'continuation_forward_differential': (trace_context+['paid','word'],0),
        'continuation_backward_differential': (trace_context+['word'],0),
        'continuation_relation_retract': (trace_context+['paid','word'],0),
        'continuation_generator_retract': (trace_context+['paid','word'],0),
        'continuationHomotopyMap': (trace_context,0),
        'continuation_homotopy_generator': (trace_context+['paid','word'],0),
        'continuation_homotopy_relation': (trace_context+['paid','word'],0),
        'continuationCochainMap': (trace_context+['paid'],0),
        'continuationCochainHomotopyEquiv': (trace_context+['paid'],0),
        'continuationDerivedCofiber': (trace_context+['paid'],0),
        'continuation_derived_zero': (trace_context+['paid'],0),
        'cofinal_tick_derived_write': (native_context,0),
        'actual_paid_stage_count': (actual_context,0),
        'actual_paid_derived_continuation': (actual_context+['index'],0),
    }
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'original paid retraction, derived cofiber and native active telescope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==counts['safe']==112 and
            stage['inherited']==0 and stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and
            counts['inductive_generated_CIs']==0,'full fresh logical CI coverage drift')
    ancestry = report['original_paid_derived_data_ancestry']
    require(ancestry==inputs['original_paid_derived_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'original paid retraction, same transition derived cofiber and four literal R stages ancestry drift')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('repo','compiled-root','base-lean-path-file','output'):
        parser.add_argument('--'+option,type=Path,required=True)
    parser.add_argument('--source-root',type=Path)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--verify-inputs-only',action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    inputs, roots, actual = verify_inputs(package,args)
    output = args.output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    save(output/'provenance.json',{'schema':'cp748-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
         'paid_direct_imports':5,'paid_project_imports':4,'gate_only_project_imports':2,'pinned_mathlib_imports':1,'new_mathlib_support_bindings':1,'inherited_mathlib_support_bindings':17,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':296,'legacy_project_bindings':88,'inherited_parent_references':292,'added_paid_parent_rows':4,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None, 'paid_direct_imports':5,'paid_project_imports':4,'gate_only_project_imports':2,'pinned_mathlib_imports':1,'new_mathlib_support_bindings':1,'inherited_mathlib_support_bindings':17,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':296,'legacy_project_bindings':88,'inherited_parent_references':292,'added_paid_parent_rows':4,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'lean_calls':0}))
        return

    lean = args.lean or Path(subprocess.check_output(['elan','which','lean'],cwd=args.repo/'Lean',text=True).strip())
    env = {**os.environ,'LEAN_PATH':os.pathsep.join(map(str,roots)),'LEAN_SYSROOT':str(lean.parent.parent)}
    cost = output/'cost.json'
    require(not cost.exists(),'use an empty output directory for a fresh run')
    calls = []

    def run(label, filename, command, scope_env):
        source = package/filename
        log = output/(label+'.log')
        start = time.monotonic()
        with log.open('wb') as stream:
            child = subprocess.Popen(command,cwd=package,env=scope_env,stdout=stream,stderr=subprocess.STDOUT)
            print(json.dumps({'label':label,'pid':child.pid}),flush=True)
            code = child.wait()
        row = {'label':label,'exit_code':code,'elapsed_seconds':time.monotonic()-start,
               'source_sha256':sha(source),'log_sha256':sha(log)}
        calls.append(row)
        save(output/(label+'.receipt.json'),row)
        save(cost,{'schema':'cp748-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP748_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp748-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
