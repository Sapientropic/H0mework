#!/usr/bin/env python3
"""Verify the original strict cochain limit, whole cocone action, and literal paid tick."""
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
            'CP751 inherited verified Kummer graph authority drift')
    for row in graft['rows']:
        selected_object = selected(row['module'],roots)[0]
        require(all(selected_object.samefile(path) for path in (row['first_hit'],row['lake_object'])) and
                sha(selected_object)==row['lake_object_sha256'] and
                sha(row['source'])==row['source_sha256'] and sha(row['trace'])==row['trace_sha256'] and
                Path(row['lake_object']).with_suffix('.olean.hash').read_text().strip()==row['object_lake_hash'],
                'CP751 inherited Kummer source, trace or first-hit drift '+row['module'])


def verify_original_signed_module(repo, revision, row, roots):
    manifest_path, verdict_path, old_manifest_path, old_verdict_path, source_copy = map(exact,row['bindings'])
    manifest, verdict, older, old_verdict = map(read,(manifest_path,verdict_path,old_manifest_path,old_verdict_path))
    module = row['module']
    original = manifest['closure'][module]
    earlier = older['closure'][module]
    reuse, = manifest['reuse_artifacts'][module]
    prior_reuse, = older['reuse_artifacts'][module]
    authority = exact(row['authority_object'])
    source = repo/row['main']
    selected_object = selected(module,roots)[0]
    require(verdict['checkpoint']=='CP267' and old_verdict['checkpoint']=='CP266' and
            verdict['verdict']==old_verdict['verdict']=='certified' and
            exact(verdict['manifest'])==manifest_path and exact(old_verdict['manifest'])==old_manifest_path and
            verdict['fixed_head']==manifest['head']==row['tracked_source_commit'] and
            old_verdict['fixed_head']==older['head'] and
            original['file']==earlier['file']==row['main'] and original['imports']==earlier['imports'] and
            original['source']==row['source_evidence']['path']==str(source_copy) and
            tracked_source_sha(repo,manifest['head'],source)==tracked_source_sha(repo,revision,source)==
                sha(source)==sha(source_copy)==original['sha256']==earlier['sha256']==row['source_sha256'] and
            reuse['source']==prior_reuse['snapshot'] and reuse['snapshot']==str(authority) and
            sha(authority)==reuse['sha256']==prior_reuse['sha256']==row['object_sha256'] and
            all(selected_object.samefile(path) for path in (authority,row['object'],row['provider'])),
            'CP751 exact original CP267 source or selected signed object drift '+module)


def verify_lake_support(repo, revision, row, roots, known_imports):
    plan_path, audit_path, input_path, trace_path, auditor = map(exact,row['bindings'])
    module = row['module']
    planned = read(plan_path)
    plan, = [item for item in (planned if isinstance(planned,list) else [planned]) if item['module']==module]
    audited, = [item for item in read(audit_path) if item['module']==module]
    fields, = [line.split('\t') for line in input_path.read_text().splitlines()
               if line.split('\t',1)[0]==module]
    _, source_name, built_name, source_lake_hash, object_lake_hash = fields
    source = repo/row['main']
    object_path = Path(built_name)
    trace = read(trace_path)
    dependencies = dict(dict(trace['inputs'])['deps'])['imports']
    trace_imports = [name.removesuffix(':importAllArts') for name,_ in dependencies if name.endswith(':importAllArts')]
    actual_imports = [name for name in row['actual_imports'] if name!='Init']
    artifact = selected(module,roots)[0]
    require(auditor.name=='GraftAudit.lean' and row['binding_kind']=='exact-lake-trace-reuse' and
            all(row[key]==plan[key] for key in ('module','main','source_sha256','tracked_source_commit',
                'object','provider','object_sha256','lake_source_hash','lake_object_hash')) and
            audited=={'module':module,'source_lake_hash':source_lake_hash,'object_lake_hash':object_lake_hash,
                'imports':row['actual_imports']} and plan['raw_imports_expected']==row['actual_imports'] and
            actual_imports==trace_imports and set(actual_imports)<=known_imports and
            source_name==str(source) and
            tracked_source_sha(repo,row['tracked_source_commit'],source)==tracked_source_sha(repo,revision,source)==
                sha(source)==row['source_sha256'] and
            trace_path.samefile(plan['lake_trace']) and sha(trace_path)==plan['lake_trace_sha256'] and
            not trace['synthetic'] and [source_name,source_lake_hash] in trace['inputs'] and
            source_lake_hash==row['lake_source_hash'] and object_lake_hash==row['lake_object_hash'] and
            trace['outputs']['o']==[object_lake_hash+'.olean'] and
            object_path.with_suffix('.olean.hash').read_text().strip()==object_lake_hash and
            all(artifact.samefile(path) for path in (object_path,row['object'],row['provider'])) and
            sha(artifact)==row['object_sha256'],
            'CP751 original Lake source, artifact, or raw import evidence drift '+module)


def verify_paid_limit_parents(repo, package, inputs, stage, context, roots):
    compact = read(exact(inputs['paid_parent_evidence'],package))
    require(compact['schema']=='cofinal-derived-stage-limit-paid-parent-evidence/v1','CP751 compact parent evidence drift')
    revision = stage['foundation_commit']
    prior = repo/'Verification/no-island/cofinal-paid-cochain-homology'
    inherited = compact['inherited_authority']
    evidence = exact(inherited['evidence'],repo)
    require(inherited['rows']==304 and inherited['commit']==revision=='47d6662029979755b300a24ffce07e537bc9fd4a' and
            evidence==prior/'evidence/paid-parents.json','CP750 signed parent evidence drift')
    paths = [prior/name for name in ('manifest.json','certificate.json','inputs.json','certify.py','independent-cost.json','audit-summary.json')]
    for path in (*paths,evidence):
        require(sha(path)==tracked_source_sha(repo,revision,path),'CP750 tracked authority drift '+str(path))
    manifest_path,cert_path,prior_inputs_path,_,cost_path,audit_path = paths
    manifest,cert,prior_inputs,cost,audit = map(read,(manifest_path,cert_path,prior_inputs_path,cost_path,audit_path))
    require(sha(manifest_path)=='11469dee82d7b1e19865a4e3c396ce3d082ab78367c39e097c9bf3ae4727adcb' and
            sha(cert_path)=='a702837ac82a018ad1f4b4f1fb86a24971e2721d2b1465857f286c3ad516758e' and
            manifest['checkpoint']==cert['checkpoint']=='CP750' and cert['verdict']=='certified' and
            set(cert['axioms'])==set(audit['axioms'])==AXIOMS and cert['inputs']['sha256']==sha(prior_inputs_path) and
            cert['paid_parent_evidence']==prior_inputs['paid_parent_evidence'] and exact(cert['paid_parent_evidence'],prior)==evidence and
            cert['independent_cost']['sha256']==sha(cost_path) and cert['audit_summary']['sha256']==sha(audit_path) and
            (cert['counts']['safe'],cert['counts']['private'],cert['counts']['extras'])==(71,44,741) and
            cert['counts']['paid_reused_project_bodies']==304 and cert['counts']['inherited_mathlib_support_bindings']+cert['counts']['new_mathlib_support_bindings']==22 and
            audit['accepted'] and audit['kernel_calls']==cost['kernel_calls']==71 and
            cost['old_ci_replays']==cost['old_source_recompiles']==0 and
            [(r['label'],r['exit_code']) for r in cost['calls'] if r['exit_code']==0]==[('001-audit',0),('003-gate',0)],
            'CP750 signed proof, independent receipt or paid scope drift')
    for path in (*paths[1:],evidence):
        member, = [row for row in manifest['members'] if row['path']==path.relative_to(prior).as_posix()]
        require(exact(member,prior)==path,'CP750 original manifest member drift '+str(path))
    static = cert['default_main_static']
    prior_independent = roots[0].parent.parent/'iqa-cofinal-paid-cochain-homology-independent'
    require(static['verdict']=='exact-inputs-verified' and static['formal_sources'] and static['calls'][-1]['exit_code']==0 and
            static['lean_calls']==static['calls'][-1]['lean_calls']==0 and
            sha(prior_independent/'main-static/provenance.json')==static['sha256'] and
            sha(prior_independent/'main-static.log')==static['calls'][-1]['log_sha256'],
            'CP750 accepted static provenance drift')
    for row in cost['calls']:
        if row['exit_code']==0:
            require(sha(prior_independent/(row['label']+'.receipt.json'))==row['receipt_sha256'] and
                    sha(prior_independent/(row['label']+'.log'))==row['log_sha256'],
                    'CP750 accepted Lean receipt drift '+row['label'])

    require(audit['raw_CIs']==audit['logical_CIs']==audit['kernel_calls']==71 and
            audit['inherited_generated_full_CIs']==audit['compiler_runtime']==audit['inductive_generated_CIs']==[],
            'CP750 independent all-fresh logical scope drift')

    paid_path = exact(stage['paid_parent_bindings'])
    paid = read(paid_path)
    rows = paid['rows']
    require(paid['schema']=='cofinal-derived-stage-limit-paid-parents/v1' and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(rows)==len({row['module'] for row in rows})==314 and rows==context['exact_paid_bodies'] and
            rows[304:]==compact['added_rows'] and compact['selected_lean_path']==paid['selected_lean_path'] and
            paid['old_compilations']==paid['copies']==context['old_objects_copied']==0,
            'CP751 exact paid inventory or aliases drift')
    m,c,promotion_path,prior_stage_path,_ = map(exact,rows[304]['bindings'])
    require(m==manifest_path and c==cert_path and sha(promotion_path)==cert['main_promotion']['sha256'] and
            sha(prior_stage_path)==prior_inputs['frozen_inputs']['stage-map.json']==
                '484efea0a923a39e6dcbffd76767c018cac3882b5e46cb8e13957a3f1d4b3d53',
            'CP750 exact promoted topology source chain drift')
    prior_stage = read(prior_stage_path)
    prior_context_path = exact(prior_stage['context'])
    prior_context = read(prior_context_path)
    prior_paid_path = exact(prior_stage['paid_parent_bindings'])
    prior_paid = read(prior_paid_path)
    require(sha(prior_context_path)==prior_inputs['frozen_inputs']['context.json'] and
            sha(prior_paid_path)==prior_inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(prior_paid['rows'])==304 and prior_paid['rows']==prior_context['exact_paid_bodies'] and
            prior_paid['old_compilations']==prior_paid['copies']==prior_context['old_objects_copied']==0 and
            context['goldbach_closure_graft']==prior_context['goldbach_closure_graft'] and
            sha(exact(context['goldbach_closure_graft']))==prior_inputs['frozen_inputs']['goldbach-closure-graft.json']==
                inputs['frozen_inputs']['goldbach-closure-graft.json'],
            'CP750 signed parent facts or prior Goldbach graph evidence drift')
    for current,old in zip(rows[:304],prior_paid['rows'],strict=True):
        module = current['module']
        artifact = selected(module,roots)[0]
        require(current=={**old,'object':current['object'],'provider':current['provider']} and
                all(artifact.samefile(p) for p in (current['object'],current['provider'],old['object'],old['provider'])) and
                sha(artifact)==old['object_sha256'] and sha(repo/old['main'])==old['source_sha256'],
                'CP751 inherited CP750 exact binding drift '+module)

    promotion = read(promotion_path)
    require(promotion['exact'] and promotion['old_compilations']==0 and
            promotion['stage_map_sha256']==sha(prior_stage_path) and len(promotion['inputs'])==len(prior_stage['inputs'])==4,
            'CP750 exact promotion scope drift')
    for row,owner,promoted,ending,attempt in zip(rows[304:308],prior_stage['inputs'],promotion['inputs'],
            ('Settlement','Cohomology','Naturality','PaidCohomology'),
            ('002','002','004','002'),strict=True):
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
                'CP750 exact source, strict compile and selected inode drift '+module)
    verify_inherited_kummer_graft(context,prior_context,inputs,prior_inputs,roots,read(exact(stage['construction_cost'])))
    mathlib = read(exact(context['mathlib_bindings']))['rows']
    require(len(mathlib)==32 and mathlib[:22]==read(exact(prior_context['mathlib_bindings']))['rows'] and
            all(selected(row['module'],roots)[0].samefile(exact(row['object'])) and exact(row['source']).is_file()
                for row in mathlib[:22]), 'CP751 exact inherited Mathlib provider drift')
    mathlib_root = repo/'Lean/.lake/packages/mathlib'
    mathlib_new = ('Mathlib.Algebra.Category.ModuleCat.Abelian','Mathlib.Algebra.Category.ModuleCat.Biproducts',
        'Mathlib.Algebra.Category.ModuleCat.Limits','Mathlib.Algebra.Category.ModuleCat.Products',
        'Mathlib.Algebra.Homology.DerivedCategory.Basic','Mathlib.Algebra.Homology.DerivedCategory.ShortExact',
        'Mathlib.Algebra.Homology.Embedding.ExtendHomotopy','Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone',
        'Mathlib.Algebra.Homology.ShortComplex.ShortExact','Mathlib.CategoryTheory.Functor.OfSequence')
    mathlib_direct = (mathlib_new[3],mathlib_new[8],mathlib_new[6])
    mathlib_revision = 'db584cd6d46c92f209a44c0f1c829460d327499d'
    for pin, module in zip(mathlib[22:],mathlib_new,strict=True):
        require(pin['module']==module and pin['tracked_source_commit']==mathlib_revision and
                exact(pin['source'])==mathlib_root/Path(*module.split('.')).with_suffix('.lean') and
                tracked_source_sha(mathlib_root,mathlib_revision,exact(pin['source']))==pin['source']['sha256'] and
                selected(module,roots)[0].samefile(exact(pin['object'])) and exact(pin['object']).samefile(pin['provider']),
                'CP751 exact direct or support Mathlib pin drift '+module)
    known_imports = {row['module'] for row in rows} | {row['module'] for row in mathlib}
    originals = ('LivingLawRootGeneratedSequentialHomotopyLimitKernel','LivingLawRootedAccountedUnfoldingKernel')
    for row, name in zip(rows[308:310],originals,strict=True):
        require(row['module']=='SaturationMonoid.'+name and row['role']=='CP267 exact '+name,
                'CP751 CP267 exact module scope drift')
        verify_original_signed_module(repo,revision,row,roots)
    lake_names = ('CochainMappingCoconeShortExact','CochainMappingCoconeFunctoriality',
        'LivingLawRootGeneratedSequentialHomotopyLimitEndomorphismKernel',
        'LivingLawRootGeneratedSequentialHomotopyLimitNaturalityKernel')
    for row, name in zip(rows[310:],lake_names,strict=True):
        require(row['module']=='SaturationMonoid.'+name,'CP751 Lake module scope drift')
        verify_lake_support(repo,revision,row,roots,known_imports)
    require(sum(row['binding_kind']!='exact-certified-source-reuse' for row in rows)==92,
            'CP751 exact legacy parent count drift')
    direct = []
    for ending in ('.LivingLawRootGeneratedSequentialHomotopyLimitKernel','.Cofinal.Topology.Cochain.Tower',
            '.CochainMappingCoconeShortExact','.LivingLawRootGeneratedSequentialHomotopyLimitNaturalityKernel',
            '.RootRelation.PaidCofinalCochain'):
        row, = [row for row in rows if row['module'].endswith(ending)]
        direct.append(row)
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
    require(len(science)==5 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'SequentialDifference','SequentialKernel','DerivedLimit','DerivedNaturality','PaidDerivedStageLimit'} and
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
    paid,direct,mathlib_direct=verify_paid_limit_parents(args.repo,package,inputs,stage,context,roots)
    imports={m for row in science.values() for m in row['base']} - science.keys()
    require(imports==set(inputs['audit_base']),'CP751 exact direct import scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    parent_view=base.parent/'iqa-cofinal-paid-cochain-homology/lean-path.txt'
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
    require(imports==set(direct)|set(mathlib_direct),'CP751 exact production import drift')
    gate_imports=re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)
    fixed_target, = [row['module'] for row in paid['rows'] if row['role']=='CP747 exact TopologyContinuation']
    division, = [row['module'] for row in paid['rows']
                 if row['module'].endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction')]
    require(gate_imports==[inputs['entry'],fixed_target,division] and not ({division,fixed_target} & imports),
            'CP751 independent fixed-target and original Division Gate-only import drift')
    construction = read(exact(stage['construction_cost']))
    profile = construction['dependent_let_cleanup_profile']
    sample = exact(profile)
    record = read(exact(profile['record']))
    require(sample.name=='Actual-002.sample.txt.zst' and profile['bytes']==8621 and
            profile['uncompressed_bytes']==311121 and profile['kind']=='dependent-let cleanup' and
            profile['before_pass_seconds']==26.9 and profile['after_pass_seconds']==0.0000213 and
            profile['before_attempt']=='002' and profile['after_attempt']=='003' and profile['math_source_unchanged'] and
            profile['source_changes']==['single-declaration cleanup.letToHave false'] and
            record=={key:value for key,value in profile.items() if key!='record'},
            'CP751 exact original dependent-let sample and diagnosis drift')
    actual_attempts = [row for row in construction['source_attempts'] if row['stage']=='Actual']
    require([(row['attempt'],row['exit_code']) for row in actual_attempts]==[('001',1),('002',0),('003',0)],
            'CP751 actual before and after strict attempt scope drift')
    _, before, after = actual_attempts
    for row, marker in ((before,'let-to-have transformation 26.9s'),(after,'let-to-have transformation 0.0213ms')):
        receipt = read(exact(row['receipt']))
        snapshot = Path(row['source']['snapshot'])
        require(receipt['exit_code']==receipt['old_compilations']==0 and receipt['source_unchanged'] and
                set(FLAGS[:3]) <= set(receipt['command']) and
                sha(snapshot)==row['source']['sha256']==receipt['source_sha256'] and marker in exact(row['log']).read_text(),
                'CP751 exact actual strict snapshot or transformation time drift')
    scoped_option = (
        b'-- Preserve the dependent let chain while checking the original receipt.\n'
        b'set_option cleanup.letToHave false in\n'
    )
    before_bytes = Path(before['source']['snapshot']).read_bytes()
    after_bytes = Path(after['source']['snapshot']).read_bytes()
    require(after_bytes.count(scoped_option)==1 and after_bytes.replace(scoped_option,b'',1)==before_bytes,
            'CP751 scoped dependent-let option must preserve the original proof bytes')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='cofinal-derived-stage-limit-compiler-companions/v1' and
            companions['companions']==inputs['compiler_companions'] and len(companions['companions'])==1 and
            companions['companions'][0]['name'].endswith('.sequentialPreimage._unsafe_rec') and
            not companions['companions'][0]['logical_use'],
            'CP751 unexpected compiler runtime companion scope')
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
    require(len(expected_runtime)==counts['compiler_runtime']==1 and
            sorted(expected_runtime,key=lambda r:r['name'])==sorted(stage['compiler_runtime'],key=lambda r:r['name']),
            'exact compiler companion CI or logical separation drift')
    require(counts['raw_private']==44 and counts['private']==43, 'private logical scope drift')
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
    face = ['Root','occurrence','face']
    source = ['Root','root','p','source']
    action = ['Root','NextRoot','root','next','p','source','target','action']
    public = {
        'difference_epi_of_surjective': (face+['onto'],0),
        'limitProductMap': (face+['cone'],0),
        'limit_product_projection': (face+['cone','stage'],0),
        'limitProductKernel': (face+['cone','lim'],0),
        'limitDifferenceSequence': (face+['cone'],0),
        'limit_difference_short_exact': (face+['cone','lim','onto'],0),
        'cochainDerivedLimitFace': (source,0),
        'cochain_derived_limit_root': (source,0),
        'cochainDerivedLimitMap': (source,0),
        'cochain_derived_limit_quasiIso': (source,0),
        'cochain_derived_limit_stage': (source+['stage'],0),
        'cochainDerivedAction': (action,0),
        'cochain_derived_limit_naturality': (action,0),
        'cochain_derived_action_quasiIso': (action,0),
        'actual_paid_derived_stage_limit': (['observation','nontrivial','half','depth','ordinal','index','p','stage'],0),
    }
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'original strict kernel, full cocone action and literal paid tick telescope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==counts['safe']==101 and
            stage['inherited']==0 and stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and
            counts['inductive_generated_CIs']==0,'full fresh logical CI coverage drift')
    ancestry = report['original_paid_derived_stage_limit_ancestry']
    require(ancestry==inputs['original_paid_derived_stage_limit_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'original difference, comparison, full cocone and literal paid cofiber ancestry drift')
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
    save(output/'provenance.json',{'schema':'cp751-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
         'paid_direct_imports':8,'paid_project_imports':5,'gate_only_project_imports':2,'pinned_mathlib_imports':3,'new_mathlib_support_bindings':10,'inherited_mathlib_support_bindings':22,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':314,'legacy_project_bindings':92,'inherited_parent_references':304,'added_paid_parent_rows':10,'tracked_lake_support_bindings':4,'signed_original_support_bindings':2,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None, 'paid_direct_imports':8,'paid_project_imports':5,'gate_only_project_imports':2,'pinned_mathlib_imports':3,'new_mathlib_support_bindings':10,'inherited_mathlib_support_bindings':22,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':314,'legacy_project_bindings':92,'inherited_parent_references':304,'added_paid_parent_rows':10,'tracked_lake_support_bindings':4,'signed_original_support_bindings':2,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp751-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP751_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp751-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
