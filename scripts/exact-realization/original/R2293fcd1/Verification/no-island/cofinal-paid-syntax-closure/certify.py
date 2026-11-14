#!/usr/bin/env python3
"""Verify the original paid syntax closure, quotient and native R model successor."""
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
            'CP746 inherited verified Kummer graph authority drift')
    for row in graft['rows']:
        selected_object = selected(row['module'],roots)[0]
        require(all(selected_object.samefile(path) for path in (row['first_hit'],row['lake_object'])) and
                sha(selected_object)==row['lake_object_sha256'] and
                sha(row['source'])==row['source_sha256'] and sha(row['trace'])==row['trace_sha256'] and
                Path(row['lake_object']).with_suffix('.olean.hash').read_text().strip()==row['object_lake_hash'],
                'CP746 inherited Kummer source, trace or first-hit drift '+row['module'])


def verify_paid_syntax_parents(repo, package, inputs, stage, context, roots):
    compact = read(exact(inputs['paid_parent_evidence'],package))
    require(compact['schema']=='cofinal-paid-syntax-closure-paid-parent-evidence/v1','CP746 compact parent evidence drift')
    revision = stage['foundation_commit']
    prior = repo/'Verification/no-island/cofinal-paid-native-trace'
    inherited = compact['inherited_authority']
    evidence = exact(inherited['evidence'],repo)
    require(inherited['rows']==281 and inherited['commit']==revision=='9d9503aad5f4d8654b9344e6c2bcbbb6900823a2' and
            evidence==prior/'evidence/paid-parents.json','CP745 signed parent evidence drift')
    paths = [prior/name for name in ('manifest.json','certificate.json','inputs.json','certify.py','independent-cost.json','audit-summary.json')]
    for path in (*paths,evidence):
        require(sha(path)==tracked_source_sha(repo,revision,path),'CP745 tracked authority drift '+str(path))
    manifest_path,cert_path,prior_inputs_path,_,cost_path,audit_path = paths
    manifest,cert,prior_inputs,cost,audit = map(read,(manifest_path,cert_path,prior_inputs_path,cost_path,audit_path))
    require(sha(manifest_path)=='008230e91ac491af681e1aff9adfc1cf3e39d9ce51aba93c15d698c64463c589' and
            sha(cert_path)=='e7ba54122e4763da2a3a41ece795e76abff87a33e2835e9ebaddd014a7188435' and
            manifest['checkpoint']==cert['checkpoint']=='CP745' and cert['verdict']=='certified' and
            set(cert['axioms'])==set(audit['axioms'])==AXIOMS and cert['inputs']['sha256']==sha(prior_inputs_path) and
            cert['paid_parent_evidence']==prior_inputs['paid_parent_evidence'] and exact(cert['paid_parent_evidence'],prior)==evidence and
            cert['independent_cost']['sha256']==sha(cost_path) and cert['audit_summary']['sha256']==sha(audit_path) and
            (cert['counts']['safe'],cert['counts']['private'],cert['counts']['extras'])==(57,12,7) and
            cert['counts']['paid_reused_project_bodies']==281 and cert['counts']['inherited_mathlib_support_bindings']+cert['counts']['new_mathlib_support_bindings']==17 and
            audit['accepted'] and audit['kernel_calls']==cost['kernel_calls']==57 and
            cost['old_ci_replays']==cost['old_source_recompiles']==0 and
            [(r['label'],r['exit_code']) for r in cost['calls'] if r['exit_code']==0]==[('001-gate',0),('003-audit',0)],
            'CP745 signed proof, independent receipt or paid scope drift')
    for path in (*paths[1:],evidence):
        member, = [row for row in manifest['members'] if row['path']==path.relative_to(prior).as_posix()]
        require(exact(member,prior)==path,'CP745 original manifest member drift '+str(path))
    static = cert['default_main_static']
    prior_independent = roots[0].parent.parent/'iqa-cofinal-paid-trace-independent'
    require(static['verdict']=='exact-inputs-verified' and static['formal_sources'] and static['calls'][-1]['exit_code']==0 and
            static['lean_calls']==static['calls'][-1]['lean_calls']==0 and
            sha(prior_independent/'main-static/provenance.json')==static['sha256'] and
            sha(prior_independent/'main-static.log')==static['calls'][-1]['log_sha256'],
            'CP745 accepted static provenance drift')
    for row in cost['calls']:
        if row['exit_code']==0:
            require(sha(prior_independent/(row['label']+'.receipt.json'))==row['receipt_sha256'] and
                    sha(prior_independent/(row['label']+'.log'))==row['log_sha256'],
                    'CP745 accepted Lean receipt drift '+row['label'])

    inherited_runtime = cert['compiler_companions']
    raw_body = prior_independent/'private-bodies.json'
    require(sha(raw_body)==audit['raw_body_report']['sha256'] and
            [row['name'].rsplit('.',2)[-2:] for row in inherited_runtime]==
                [['expression','_unsafe_rec'],['trace','_unsafe_rec']] and
            inherited_runtime==audit['compiler_runtime']==read(raw_body)['stages'][0]['compiler_runtime'] and
            all(row['isPartial'] and not row['isUnsafe'] and row['nonself_incoming_edges']==0
                for row in inherited_runtime),
            'CP745 exact inherited compiler-only companion scope drift')

    paid_path = exact(stage['paid_parent_bindings'])
    paid = read(paid_path)
    rows = paid['rows']
    require(paid['schema']=='cofinal-paid-closure-paid-parents/v1' and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(rows)==len({row['module'] for row in rows})==286 and rows==context['exact_paid_bodies'] and
            rows[281:]==compact['added_rows'] and compact['selected_lean_path']==paid['selected_lean_path'] and
            paid['old_compilations']==paid['copies']==context['old_objects_copied']==0,
            'CP746 exact paid inventory or aliases drift')
    m,c,promotion_path,prior_stage_path,_ = map(exact,rows[-1]['bindings'])
    require(m==manifest_path and c==cert_path and sha(promotion_path)==cert['main_promotion']['sha256'] and
            sha(prior_stage_path)==prior_inputs['frozen_inputs']['stage-map.json']==
                '47f6e5ea8524c535527a76e09e5a29f09eb689edf86fb925b94ac676a649f559',
            'CP745 exact promoted topology source chain drift')
    prior_stage = read(prior_stage_path)
    prior_context_path = exact(prior_stage['context'])
    prior_context = read(prior_context_path)
    prior_paid_path = exact(prior_stage['paid_parent_bindings'])
    prior_paid = read(prior_paid_path)
    require(sha(prior_context_path)==prior_inputs['frozen_inputs']['context.json'] and
            sha(prior_paid_path)==prior_inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(prior_paid['rows'])==281 and prior_paid['rows']==prior_context['exact_paid_bodies'] and
            prior_paid['old_compilations']==prior_paid['copies']==prior_context['old_objects_copied']==0 and
            context['goldbach_closure_graft']==prior_context['goldbach_closure_graft'] and
            sha(exact(context['goldbach_closure_graft']))==prior_inputs['frozen_inputs']['goldbach-closure-graft.json']==
                inputs['frozen_inputs']['goldbach-closure-graft.json'],
            'CP745 signed parent facts or prior Goldbach graph evidence drift')
    for current,old in zip(rows[:281],prior_paid['rows'],strict=True):
        module = current['module']
        artifact = selected(module,roots)[0]
        require(current=={**old,'object':current['object'],'provider':current['provider']} and
                all(artifact.samefile(p) for p in (current['object'],current['provider'],old['object'],old['provider'])) and
                sha(artifact)==old['object_sha256'] and sha(repo/old['main'])==old['source_sha256'],
                'CP746 inherited CP745 exact binding drift '+module)

    promotion = read(promotion_path)
    require(promotion['exact'] and promotion['old_compilations']==0 and
            promotion['stage_map_sha256']==sha(prior_stage_path) and len(promotion['inputs'])==len(prior_stage['inputs'])==5,
            'CP745 exact promotion scope drift')
    for row,owner,promoted,ending,attempt in zip(rows[281:],prior_stage['inputs'],promotion['inputs'],
            ('Expression','Trace','Morphism','Native','TopologyTrace'),
            ('001','002','005','001','002'),strict=True):
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
                'CP745 exact source, strict compile and selected inode drift '+module)
    verify_inherited_kummer_graft(context,prior_context,inputs,prior_inputs,roots,read(exact(stage['construction_cost'])))
    mathlib = read(exact(context['mathlib_bindings']))['rows']
    require(len(mathlib)==17 and mathlib==read(exact(prior_context['mathlib_bindings']))['rows'] and
            all(selected(row['module'],roots)[0].samefile(exact(row['object'])) and exact(row['source']).is_file() for row in mathlib),
            'CP746 exact inherited Mathlib provider drift')
    require(sum(row['binding_kind']!='exact-certified-source-reuse' for row in rows)==86,
            'CP746 exact legacy parent count drift')
    direct = []
    for ending in ('.Cofinal.Topology.Operations.Trace','.History.Payment.Closure','.History.Payment.Completion',
            '.RootRelation.PaidCompletion'):
        row, = [row for row in rows if row['module'].endswith(ending)]
        direct.append(row)
    for row in direct[1:]:
        manifest_path,cert_path,promotion_path,stage_path,strict_path = map(exact,row['bindings'])
        strict = read(strict_path)
        signed = read(cert_path)
        require(row['tracked_source_commit']=='e275d03dd7cb313d9c5e9b9bca2627221ac78c7d' and
                signed['checkpoint']=='CP737' and signed['verdict']=='certified' and
                any(entry['path']=='certificate.json' and entry['sha256']==sha(cert_path)
                    for entry in read(manifest_path)['members']) and
                read(promotion_path)['stage_map_sha256']==sha(stage_path) and
                strict['exit_code']==strict['old_compilations']==0 and set(FLAGS[:3])<=set(strict['command']) and
                sha(strict['source_snapshot'])==sha(row['source_evidence']['path'])==row['source_sha256'] and
                selected(row['module'],roots)[0].samefile(exact(strict['object'])),
                'CP746 original paid closure/signed source drift '+row['module'])
    equation_owner = 'SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Consumer'
    require(inputs['generated_equation_paid_owner']==equation_owner,'CP746 generated equation paid owner drift')
    effect, = [row for row in rows if row['module']=='SaturationMonoid.GenericFoundation.Operations.Effect']
    manifest_path,signatures_path,closure_path = map(exact,effect['bindings'])
    signed_manifest,signed_scope,closure = map(read,(manifest_path,signatures_path,closure_path))
    source = signed_manifest['closure'][equation_owner]
    old = closure['closure'][equation_owner]
    reuse, = signed_manifest['reuse_artifacts'][equation_owner]
    first = selected(equation_owner,roots)[0]
    authority = Path(reuse['snapshot'])
    require(signed_scope['all_original_finalization_complete'] and signed_scope['checkpoint']=='CP267' and
            signed_scope['immutable_files']['manifest.json']==sha(manifest_path) and
            sha(manifest_path.with_name('verdict.json'))==signed_scope['immutable_files']['verdict.json'] and
            read(manifest_path.with_name('verdict.json'))['verdict']=='certified' and
            source['file']==old['file'] and source['imports']==old['imports'] and
            sha(source['source'])==source['sha256']==old['sha256']==sha(repo/source['file'])==
                tracked_source_sha(repo,revision,repo/source['file']) and
            first.samefile(authority) and first.samefile(old['loaded_artifact']) and
            str(authority)==old['formal_artifact_authority'] and sha(first)==reuse['sha256']==old['olean_sha256'],
            'CP746 exact CP267 transitive generated-equation owner drift')
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
    require(len(science)==4 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'Payment','Closure','Quotient','PaidSyntaxCompletion'} and
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
    paid,direct=verify_paid_syntax_parents(args.repo,package,inputs,stage,context,roots)
    imports={m for row in science.values() for m in row['base']} - science.keys()
    require(imports==set(inputs['audit_base']),'CP746 exact direct import scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    parent_view=base.parent/'iqa-cofinal-paid-trace/lean-path.txt'
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
    require(imports==set(direct),'CP746 exact production import drift')
    gate_imports=re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)
    division, = [row['module'] for row in paid['rows']
                 if row['module'].endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction')]
    actor, = [row['module'] for row in paid['rows'] if row['role']=='CP745 exact TopologyTrace']
    require(gate_imports==[inputs['entry'],division,actor] and not ({division,actor} & imports),
            'CP746 independent original R Division and fixed-target Gate-only import drift')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='cofinal-paid-closure-compiler-companions/v1' and
            companions['companions']==inputs['compiler_companions']==[],
            'CP746 unexpected compiler runtime companion scope')
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
            stage['fresh_replayed'] == counts['kernel_calls'] == report['fresh_safe_replayed_CIs'] and
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
    require(counts['raw_private']==counts['private']==28, 'private logical scope drift')
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
            all(r['same_full_constant_info'] and not r['kernel_replayed'] and
                r['paid_owner']==inputs['generated_equation_paid_owner']
                for r in stage['inherited_generated_full_CIs']), 'inherited CI qualification drift')
    require(not owners and report['safe_private_original_CIs'] == stage['safe_private'] == counts['safe'] and
            stage['kernel_calls'] == counts['kernel_calls'] and stage['compiler_extras'] == counts['extras'] and
            sum(r['name'].startswith('_private.') for r in stage['declarations']) == counts['private'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['source_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source provenance')
    context = ['S','V','X','_','s','old','before','after']
    paid = context+['p','paid']
    closure = ['S','Root','V','X','_','s','old','before','after','root','p','paid']
    native = ['observation','nontrivial','half','depth','ordinal','p']
    public = {
        'paymentEquiv': (paid,0),
        'word_map_payment': (paid+['charges'],0),
        'word_map_coefficientSum': (['S','V','X','_','s','p','word'],0),
        'trace_exposure': (paid,0),
        'generatorEquiv': (closure,0),
        'generator_equiv_value': (closure+['word'],0),
        'relationEquiv': (closure,0),
        'relation_equiv_value': (closure+['word'],0),
        'generator_differential_equiv': (closure+['word'],0),
        'completionEquiv': (closure,0),
        'completion_equiv_projection': (closure+['word'],0),
        'completion_equiv_coordinate': (closure+['value'],0),
        'actualPaidSyntaxCompletion': (native,0),
        'actual_paid_syntax_source_unit': (native,0),
        'actual_paid_syntax_model_next': (native+['coefficient'],0),
    }
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'original paid closure and native model telescope drift')
    equations = stage['replayed_generated_same_type_CIs']
    require([r['name'] for r in equations]==inputs['replayed_generated_same_type_CIs'] and len(equations)==1 and
            equations[0]['name'].endswith('.RootedAccountedUnfolding.map.eq_def') and
            equations[0]['replayed_as']=='CP746Audit.replayed_root_map_eq_def' and
            equations[0]['paid_owner']==inputs['generated_equation_paid_owner'] and
            equations[0]['same_type_and_levels'] and equations[0]['different_raw_value'] and
            equations[0]['kernel_replayed'] and not equations[0]['same_full_constant_info'],
            'CP746 generated theorem proof-body replay scope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==51 and
            stage['inherited']==1 and counts['safe']==52 and
            stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and
            counts['inductive_generated_CIs']==0,'full fresh and exact shared logical CI coverage drift')
    ancestry = report['original_paid_syntax_data_ancestry']
    require(ancestry==inputs['original_paid_syntax_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'original paid generator, relation, quotient and native next ancestry drift')
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
    save(output/'provenance.json',{'schema':'cp746-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
         'paid_direct_imports':4,'paid_project_imports':4,'gate_only_project_imports':2,'pinned_mathlib_imports':0,'new_mathlib_support_bindings':0,'inherited_mathlib_support_bindings':17,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':286,'legacy_project_bindings':86,'inherited_parent_references':281,'added_paid_parent_rows':5,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None, 'paid_direct_imports':4,'paid_project_imports':4,'gate_only_project_imports':2,'pinned_mathlib_imports':0,'new_mathlib_support_bindings':0,'inherited_mathlib_support_bindings':17,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':286,'legacy_project_bindings':86,'inherited_parent_references':281,'added_paid_parent_rows':5,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp746-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP746_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp746-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
