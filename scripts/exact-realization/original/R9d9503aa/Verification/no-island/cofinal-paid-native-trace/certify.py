#!/usr/bin/env python3
"""Verify the original paid trace interpretation and the fixed-target active and terminal receipts."""
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
            'CP745 inherited verified Kummer graph authority drift')
    for row in graft['rows']:
        selected_object = selected(row['module'],roots)[0]
        require(all(selected_object.samefile(path) for path in (row['first_hit'],row['lake_object'])) and
                sha(selected_object)==row['lake_object_sha256'] and
                sha(row['source'])==row['source_sha256'] and sha(row['trace'])==row['trace_sha256'] and
                Path(row['lake_object']).with_suffix('.olean.hash').read_text().strip()==row['object_lake_hash'],
                'CP745 inherited Kummer source, trace or first-hit drift '+row['module'])


def verify_historical_operation(repo, foundation, row, module, roots):
    signed_commit = 'd750d166ac58a4cfbaaef1c6a0abcfc33b285ad3'
    require(row['module']==module and row['binding_kind']=='exact-historical-source-object-reuse' and
            row['tracked_source_commit']==signed_commit and row['source_evidence']['kind']=='retained-source',
            'CP267 exact original operation source scope drift')
    manifest_path, signatures_path, closure_path = map(exact,row['bindings'])
    signatures, manifest, closure = map(read,(signatures_path,manifest_path,closure_path))
    verdict_path = exact({'path':str(manifest_path.with_name('verdict.json')),
                          'sha256':signatures['immutable_files']['verdict.json']})
    verdict = read(verdict_path)
    require(signatures['all_original_finalization_complete'] and signatures['checkpoint']==verdict['checkpoint']=='CP267' and
            signatures['immutable_files']['manifest.json']==sha(manifest_path)==verdict['manifest']['sha256'] and
            exact(verdict['manifest'])==manifest_path and
            signatures['capsule_sha256']==manifest['capsule_sha256']==verdict['capsule_sha256'] and
            manifest['head']==verdict['fixed_head']==signed_commit and verdict['verdict']=='certified',
            'CP267 signed original operation closure drift')
    original = manifest['closure'][module]
    actual = closure['closure'][module]
    source = repo/row['main']
    artifact = selected(module,roots)[0]
    authority = exact(row['authority_object'])
    reuse, = manifest['reuse_artifacts'][module]
    require(original['file']==actual['file']==row['main'] and original['imports']==actual['imports'] and
            original['source']==row['source_evidence']['path'] and
            tracked_source_sha(repo,signed_commit,source)==
                tracked_source_sha(repo,foundation,source)==sha(source)==sha(original['source'])==
                original['sha256']==actual['sha256']==row['source_sha256'] and
            actual['formal_artifact_authority']==str(authority)==reuse['snapshot'] and
            actual['loaded_artifact']==row['provider'] and
            sha(artifact)==reuse['sha256']==actual['olean_sha256']==row['object_sha256'] and
            all(artifact.samefile(path) for path in (authority,row['provider'],row['object'])),
            'CP745 operation source, signed object, or first-hit identity drift')


def verify_goldbach_consumer(repo, revision, native, context, roots):
    actor = native['module']
    verdict_path,manifest_path,reconcile_path,graft_path,signed_actor,cp72_manifest,cp72_reconcile,cp72_actor = map(exact,native['bindings'])
    verdict,manifest,reconcile,graft = map(read,(verdict_path,manifest_path,reconcile_path,graft_path))
    require(native['binding_kind']=='exact-signed-inherited-source-reuse' and
            verdict['checkpoint']=='CP74' and verdict['verdict']=='certified' and
            verdict['fixed_head']==manifest['head']=='eb5168b7d73160f2ee2f79bc7c1dfe5de30b74f5' and
            verdict['trust']['manifest']['sha256']==sha(manifest_path) and
            {'-t','0','-DwarningAsError=true'}<=set(verdict['trust']['flags']) and
            set(verdict['axioms']['allowed_only'])==AXIOMS and
            verdict['prior_binding']['final_shared_source_import_and_artifact_equal'] and
            reconcile['current_nonowned_source_mismatches']==reconcile['formal_cp73_artifact_mismatches']==[] and
            graft_path==exact(context['goldbach_closure_graft']) and
            graft['signed_manifest']==str(manifest_path) and graft['manifest_sha256']==sha(manifest_path),
            'CP745 direct CP74 fixed-target source signature drift')
    previous, receipt = map(read,(cp72_manifest,cp72_reconcile))
    original, = [row for row in receipt['fresh'] if row['module']==actor]
    earlier = manifest['cp72_verdict']
    cp72_old_root = Path(previous['overlay'])
    def cp72_path(path):
        return cp72_manifest.parent/Path(path).relative_to(cp72_old_root)
    current = selected(actor,roots)[0]
    tracked = repo/native['main']
    grafted, = [row for row in graft['rows'] if row['module']==actor]
    require(earlier['commit']==native['tracked_source_commit']=='61038acb9f0958c12ebab344f48471d115e7296a' and
            {k:earlier[k] for k in ('path','sha256')} in verdict['prior_signed_checkpoints'] and
            original['exit_code']==0 and {'-t','0','-DwarningAsError=true'}<=set(original['command']) and
            sha(cp72_path(original['log']))==original['log_sha256'] and cp72_path(original['olean'])==cp72_actor and
            sha(current)==sha(cp72_actor)==sha(signed_actor)==original['olean_sha256']==native['object_sha256']==grafted['object_sha256'] and
            previous['closure'][actor]['imports']==manifest['closure'][actor]['imports'] and
            sha(cp72_path(previous['closure'][actor]['source']))==previous['closure'][actor]['sha256']==
                original['source_sha256']==native['source_sha256']==grafted['source_sha256']==
                sha(native['source_evidence']['path'])==sha(tracked)==tracked_source_sha(repo,revision,tracked)==
                tracked_source_sha(repo,earlier['commit'],tracked) and
            grafted['copied_bytes']==0 and exact(native['signed_ancestor_object'])==signed_actor and
            all(current.samefile(path) for path in (native['object'],native['provider'],signed_actor,
                exact(native['authority_object']),grafted['path'],grafted['signed_path'])),
            'CP745 literal original Goldbach source, strict receipt or graft inode drift')


def verify_paid_trace_parents(repo, package, inputs, stage, context, roots):
    compact = read(exact(inputs['paid_parent_evidence'],package))
    require(compact['schema']=='cofinal-paid-native-trace-paid-parent-evidence/v1','CP745 compact parent evidence drift')
    revision = stage['foundation_commit']
    prior = repo/'Verification/no-island/cofinal-native-bilinear'
    inherited = compact['inherited_authority']
    evidence = exact(inherited['evidence'],repo)
    require(inherited['rows']==275 and inherited['commit']==revision=='5094c13256b5ee1bf9a82b986565cfc81030899a' and
            evidence==prior/'evidence/paid-parents.json','CP744 signed parent evidence drift')
    paths = [prior/name for name in ('manifest.json','certificate.json','inputs.json','certify.py','independent-cost.json','audit-summary.json')]
    for path in (*paths,evidence):
        require(sha(path)==tracked_source_sha(repo,revision,path),'CP744 tracked authority drift '+str(path))
    manifest_path,cert_path,prior_inputs_path,_,cost_path,audit_path = paths
    manifest,cert,prior_inputs,cost,audit = map(read,(manifest_path,cert_path,prior_inputs_path,cost_path,audit_path))
    require(sha(manifest_path)=='e7c3a0fe43c81974ee684b2d64d78e222de88dd24a7d4b4e9547eb313be0aa6a' and
            sha(cert_path)=='9e9c76d083d2bd4361f0f0c9d79adb64e516f064abfcf472bdc56edeec82714e' and
            manifest['checkpoint']==cert['checkpoint']=='CP744' and cert['verdict']=='certified' and
            set(cert['axioms'])==set(audit['axioms'])==AXIOMS and cert['inputs']['sha256']==sha(prior_inputs_path) and
            cert['paid_parent_evidence']==prior_inputs['paid_parent_evidence'] and exact(cert['paid_parent_evidence'],prior)==evidence and
            cert['independent_cost']['sha256']==sha(cost_path) and cert['audit_summary']['sha256']==sha(audit_path) and
            (cert['counts']['safe'],cert['counts']['private'],cert['counts']['extras'])==(39,16,3) and
            cert['counts']['paid_reused_project_bodies']==275 and cert['counts']['inherited_mathlib_support_bindings']+cert['counts']['new_mathlib_support_bindings']==17 and
            audit['accepted'] and audit['kernel_calls']==cost['kernel_calls']==39 and
            cost['old_ci_replays']==cost['old_source_recompiles']==0 and
            [(r['label'],r['exit_code']) for r in cost['calls'] if r['exit_code']==0]==[('001-gate',0),('002-audit',0)],
            'CP744 signed proof, independent receipt or paid scope drift')
    for path in (*paths[1:],evidence):
        member, = [row for row in manifest['members'] if row['path']==path.relative_to(prior).as_posix()]
        require(exact(member,prior)==path,'CP744 original manifest member drift '+str(path))
    static = cert['default_main_static']
    prior_independent = roots[0].parent.parent/'iqa-cofinal-native-bilinear-independent'
    require(static['verdict']=='exact-inputs-verified' and static['formal_sources'] and static['calls'][-1]['exit_code']==0 and
            static['lean_calls']==static['calls'][-1]['lean_calls']==0 and
            sha(prior_independent/'main-static/provenance.json')==static['sha256'] and
            sha(prior_independent/'main-static.log')==static['calls'][-1]['log_sha256'],
            'CP744 accepted static provenance drift')
    for row in cost['calls']:
        if row['exit_code']==0:
            require(sha(prior_independent/(row['label']+'.receipt.json'))==row['receipt_sha256'] and
                    sha(prior_independent/(row['label']+'.log'))==row['log_sha256'],
                    'CP744 accepted Lean receipt drift '+row['label'])

    paid_path = exact(stage['paid_parent_bindings'])
    paid = read(paid_path)
    rows = paid['rows']
    require(paid['schema']=='cofinal-paid-trace-paid-parents/v1' and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(rows)==len({row['module'] for row in rows})==281 and rows==context['exact_paid_bodies'] and
            rows[275:]==compact['added_rows'] and compact['selected_lean_path']==paid['selected_lean_path'] and
            paid['old_compilations']==paid['copies']==context['old_objects_copied']==0,
            'CP745 exact paid inventory or aliases drift')
    m,c,promotion_path,prior_stage_path,_ = map(exact,rows[277]['bindings'])
    require(m==manifest_path and c==cert_path and sha(promotion_path)==cert['main_promotion']['sha256'] and
            sha(prior_stage_path)==prior_inputs['frozen_inputs']['stage-map.json']==
                '46d5c37f3735e9b61162f6ba7fa949b9fb2666d47e5d55bea94fcb2051042856',
            'CP744 exact promoted topology source chain drift')
    prior_stage = read(prior_stage_path)
    prior_context_path = exact(prior_stage['context'])
    prior_context = read(prior_context_path)
    prior_paid_path = exact(prior_stage['paid_parent_bindings'])
    prior_paid = read(prior_paid_path)
    require(sha(prior_context_path)==prior_inputs['frozen_inputs']['context.json'] and
            sha(prior_paid_path)==prior_inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(prior_paid['rows'])==275 and prior_paid['rows']==prior_context['exact_paid_bodies'] and
            prior_paid['old_compilations']==prior_paid['copies']==prior_context['old_objects_copied']==0 and
            context['goldbach_closure_graft']==prior_context['goldbach_closure_graft'] and
            sha(exact(context['goldbach_closure_graft']))==prior_inputs['frozen_inputs']['goldbach-closure-graft.json']==
                inputs['frozen_inputs']['goldbach-closure-graft.json'],
            'CP744 signed parent facts or prior Goldbach graph evidence drift')
    for current,old in zip(rows[:275],prior_paid['rows'],strict=True):
        module = current['module']
        artifact = selected(module,roots)[0]
        require(current=={**old,'object':current['object'],'provider':current['provider']} and
                all(artifact.samefile(p) for p in (current['object'],current['provider'],old['object'],old['provider'])) and
                sha(artifact)==old['object_sha256'] and sha(repo/old['main'])==old['source_sha256'],
                'CP745 inherited CP744 exact binding drift '+module)

    promotion = read(promotion_path)
    require(promotion['exact'] and promotion['old_compilations']==0 and
            promotion['stage_map_sha256']==sha(prior_stage_path) and len(promotion['inputs'])==len(prior_stage['inputs'])==3,
            'CP744 exact promotion scope drift')
    for row,owner,promoted,ending,attempt in zip(rows[275:278],prior_stage['inputs'],promotion['inputs'],
            ('Bilinear','Completion','CofinalBilinear'),
            ('003','004','002'),strict=True):
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
                'CP744 exact source, strict compile and selected inode drift '+module)
    verify_inherited_kummer_graft(context,prior_context,inputs,prior_inputs,roots,read(exact(stage['construction_cost'])))
    historical = (
        'SaturationMonoid.GenericFoundation.Operations.Effect',
        'SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Append',
        'SaturationMonoid.GenericFoundation.Responsibility.Debt.Activation.Root.Direct.JointSource.OwnerFree.Completion',
    )
    for row,module in zip(rows[278:],historical,strict=True):
        verify_historical_operation(repo,revision,row,module,roots)
    mathlib = read(exact(context['mathlib_bindings']))['rows']
    require(len(mathlib)==17 and mathlib==read(exact(prior_context['mathlib_bindings']))['rows'] and
            all(selected(row['module'],roots)[0].samefile(exact(row['object'])) and exact(row['source']).is_file() for row in mathlib),
            'CP745 exact inherited Mathlib provider drift')
    require(sum(row['binding_kind']!='exact-certified-source-reuse' for row in rows)==86,
            'CP745 exact legacy parent count drift')
    direct = []
    for ending in ('.Cofinal.Topology.Bilinear.Completion','.Operations.Effect','.History.Payment','.History.Append',
            '.JointSource.OwnerFree.Completion','.Calculation.Cursor.Native.Consumer'):
        row, = [row for row in rows if row['module'].endswith(ending)]
        direct.append(row)
    payment = direct[2]
    payment_manifest,payment_certificate,payment_promotion,payment_stage,payment_receipt = map(exact,payment['bindings'])
    payment_strict = read(payment_receipt)
    require(read(payment_certificate)['verdict']=='certified' and
            any(entry['path']=='certificate.json' and entry['sha256']==sha(payment_certificate)
                for entry in read(payment_manifest)['members']) and
            read(payment_promotion)['stage_map_sha256']==sha(payment_stage) and
            payment_strict['exit_code']==payment_strict['old_compilations']==0 and
            set(FLAGS[:3])<=set(payment_strict['command']) and
            sha(payment_strict['source_snapshot'])==payment['source_sha256'] and
            selected(payment['module'],roots)[0].samefile(exact(payment_strict['object'])),
            'CP745 exact original paid word support drift')
    verify_goldbach_consumer(repo,revision,direct[-1],context,roots)
    return paid,[row['module'] for row in direct]


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
    require(len(science)==5 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'Expression','Trace','Morphism','Native','TopologyTrace'} and
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
    paid,direct=verify_paid_trace_parents(args.repo,package,inputs,stage,context,roots)
    imports={m for row in science.values() for m in row['base']} - science.keys()
    require(imports==set(inputs['audit_base']),'CP745 exact direct import scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    parent_view=base.parent/'iqa-cofinal-native-bilinear/lean-path.txt'
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
    require(imports==set(direct),'CP745 exact production import drift')
    gate_imports=re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)
    paid_bilinear, = [row['module'] for row in paid['rows'] if row['role']=='CP744 exact CofinalBilinear']
    require(gate_imports==[inputs['entry'],paid_bilinear] and paid_bilinear not in imports,
            'CP745 independent original native bilinear Gate-only import drift')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='cofinal-paid-trace-compiler-companions/v1' and
            companions['companions']==inputs['compiler_companions'] and
            [row['name'].rsplit('.',2)[-2:] for row in companions['companions']]==
                [['expression','_unsafe_rec'],['trace','_unsafe_rec']],
            'unexpected compiler runtime companion scope')
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
            report['fresh_raw_regions'] == 5 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    expected_runtime = [{'name':r['name'],'owner':r['module'],'safe_source':r['owner'],
        'isUnsafe':False,'isPartial':True,'self_edges':1,'nonself_incoming_edges':0,
        'type_preserved':True,'value_preserved':True} for r in inputs['compiler_companions']]
    require(len(expected_runtime)==counts['compiler_runtime']==2 and
            sorted(expected_runtime,key=lambda r:r['name'])==sorted(stage['compiler_runtime'],key=lambda r:r['name']),
            'exact compiler companion CI or logical separation drift')
    require(counts['raw_private']==counts['private']==12, 'private logical scope drift')
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
    expressionInputs = ['p','S','V','X','_']
    traceContext = ['S','V','X','_','p']
    traceInputs = traceContext+['old','s','before','after','paid']
    nativeInputs = ['N','V','old','origin','Sorts','Value','Var','_','sort','reader','runtime','p','active']
    public = {
        'environment': (expressionInputs+['old'],0),
        'expression': (expressionInputs+['sort','_'],0),
        'expression_eval': (expressionInputs+['sort','term','old'],0),
        'expression_effect': (expressionInputs+['sort','term','old','increment'],0),
        'expression_remaining': (traceContext+['s','term'],0),
        'step': (traceInputs,0),
        'trace': (traceInputs,0),
        'trace_length': (traceInputs,0),
        'wordMap': (traceContext+['s'],0),
        'trace_words': (traceInputs,0),
        'trace_word_at': (traceInputs+['index'],0),
        'inventoryMorphism': (['S','V','X','_','s','p','old','increment'],0),
        'inventory_read': (['S','V','X','_','s','p','old','increment','word'],0),
        'cofinal_active_tick_words': (nativeInputs,0),
        'actual_actor_cofinal_paid_tick': (['depth','count','within','p'],0),
        'actual_actor_cofinal_terminal': (['depth','p'],0),
    }
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'original paid expression, trace, and fixed-target telescope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==counts['safe']==57 and
            stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and
            counts['inductive_generated_CIs']==0,'full fresh logical CI coverage drift')
    ancestry = report['original_paid_trace_data_ancestry']
    require(ancestry==inputs['original_paid_trace_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'original ordered paid word, full inventory and fixed-target receipt ancestry drift')
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
    save(output/'provenance.json',{'schema':'cp745-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
         'paid_direct_imports':6,'paid_project_imports':6,'gate_only_project_imports':1,'pinned_mathlib_imports':0,'new_mathlib_support_bindings':0,'inherited_mathlib_support_bindings':17,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':281,'legacy_project_bindings':86,'inherited_parent_references':275,'added_paid_parent_rows':6,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None, 'paid_direct_imports':6,'paid_project_imports':6,'gate_only_project_imports':1,'pinned_mathlib_imports':0,'new_mathlib_support_bindings':0,'inherited_mathlib_support_bindings':17,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':281,'legacy_project_bindings':86,'inherited_parent_references':275,'added_paid_parent_rows':6,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp745-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP745_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp745-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
