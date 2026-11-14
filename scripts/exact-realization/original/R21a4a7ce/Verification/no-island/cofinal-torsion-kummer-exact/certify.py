#!/usr/bin/env python3
"""Verify the coherent ambient kernel and the original rational Kummer class fibre."""
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
            'CP742 inherited verified Kummer graph authority drift')
    for row in graft['rows']:
        selected_object = selected(row['module'],roots)[0]
        require(all(selected_object.samefile(path) for path in (row['first_hit'],row['lake_object'])) and
                sha(selected_object)==row['lake_object_sha256'] and
                sha(row['source'])==row['source_sha256'] and sha(row['trace'])==row['trace_sha256'] and
                Path(row['lake_object']).with_suffix('.olean.hash').read_text().strip()==row['object_lake_hash'],
                'CP742 inherited Kummer source, trace or first-hit drift '+row['module'])


def verify_kummer_coherent_kernel_parents(repo, package, inputs, stage, context, roots):
    compact = read(exact(inputs['paid_parent_evidence'],package))
    require(compact['schema']=='cofinal-torsion-kernel-paid-parent-evidence/v1','CP742 compact parent evidence drift')
    revision = stage['foundation_commit']
    prior = repo/'Verification/no-island/cofinal-torsion-kummer-completion'
    inherited = compact['inherited_authority']
    evidence = exact(inherited['evidence'],repo)
    require(inherited['rows']==264 and inherited['commit']==revision=='7cd85f357a27aaaac57ca089ea8dae2fdd9e776a' and
            evidence==prior/'evidence/paid-parents.json','CP741 signed parent evidence drift')
    paths = [prior/name for name in ('manifest.json','certificate.json','inputs.json','certify.py','independent-cost.json','audit-summary.json')]
    for path in (*paths,evidence):
        require(sha(path)==tracked_source_sha(repo,revision,path),'CP741 tracked authority drift '+str(path))
    manifest_path,cert_path,prior_inputs_path,_,cost_path,audit_path = paths
    manifest,cert,prior_inputs,cost,audit = map(read,(manifest_path,cert_path,prior_inputs_path,cost_path,audit_path))
    require(sha(manifest_path)=='a556143557f4ab287ddc2b757a86cc2e927978b562b22806e14fd619e8bbdd90' and
            sha(cert_path)=='d7758515b241adc6806b8d06f289a3e9230575c337088f356665c37105fbd3bb' and
            manifest['checkpoint']==cert['checkpoint']=='CP741' and cert['verdict']=='certified' and
            set(cert['axioms'])==set(audit['axioms'])==AXIOMS and cert['inputs']['sha256']==sha(prior_inputs_path) and
            cert['paid_parent_evidence']==prior_inputs['paid_parent_evidence'] and exact(cert['paid_parent_evidence'],prior)==evidence and
            cert['independent_cost']['sha256']==sha(cost_path) and cert['audit_summary']['sha256']==sha(audit_path) and
            (cert['counts']['safe'],cert['counts']['private'],cert['counts']['extras'])==(36,13,18) and
            cert['counts']['paid_reused_project_bodies']==264 and cert['counts']['inherited_mathlib_support_bindings']+cert['counts']['new_mathlib_support_bindings']==15 and
            audit['accepted'] and audit['kernel_calls']==cost['kernel_calls']==36 and
            cost['old_ci_replays']==cost['old_source_recompiles']==0 and
            [(r['label'],r['exit_code']) for r in cost['calls'] if r['exit_code']==0]==[('002-gate',0),('003-audit',0)],
            'CP741 signed proof, independent receipt or paid scope drift')
    for path in (*paths[1:],evidence):
        member, = [row for row in manifest['members'] if row['path']==path.relative_to(prior).as_posix()]
        require(exact(member,prior)==path,'CP741 original manifest member drift '+str(path))
    static = cert['default_main_static']
    prior_independent = roots[0].parent.parent/'iqa-cofinal-torsion-completion-independent'
    require(static['verdict']=='exact-inputs-verified' and static['formal_sources'] and static['calls'][-1]['exit_code']==0 and
            static['lean_calls']==static['calls'][-1]['lean_calls']==0 and
            sha(prior_independent/'main-static/provenance.json')==static['sha256'] and
            sha(prior_independent/'main-static.log')==static['calls'][-1]['log_sha256'],
            'CP741 accepted static provenance drift')
    for row in cost['calls']:
        if row['exit_code']==0:
            require(sha(prior_independent/(row['label']+'.receipt.json'))==row['receipt_sha256'] and
                    sha(prior_independent/(row['label']+'.log'))==row['log_sha256'],
                    'CP741 accepted Lean receipt drift '+row['label'])

    paid_path = exact(stage['paid_parent_bindings'])
    paid = read(paid_path)
    rows = paid['rows']
    require(paid['schema']=='cofinal-torsion-kernel-paid-parents/v1' and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(rows)==len({row['module'] for row in rows})==268 and rows==context['exact_paid_bodies'] and
            rows[264:]==compact['added_rows'] and compact['selected_lean_path']==paid['selected_lean_path'] and
            paid['old_compilations']==paid['copies']==context['old_objects_copied']==0,
            'CP742 exact paid inventory or aliases drift')
    m,c,promotion_path,prior_stage_path,_ = map(exact,rows[-1]['bindings'])
    require(m==manifest_path and c==cert_path and sha(promotion_path)==cert['main_promotion']['sha256'] and
            sha(prior_stage_path)==prior_inputs['frozen_inputs']['stage-map.json']==
                'b3a8097909d3f42ef1296630c16fcc30123e90b5b96ae358498ca3704b6bf24a',
            'CP741 exact promoted topology source chain drift')
    prior_stage = read(prior_stage_path)
    prior_context_path = exact(prior_stage['context'])
    prior_context = read(prior_context_path)
    prior_paid_path = exact(prior_stage['paid_parent_bindings'])
    prior_paid = read(prior_paid_path)
    require(sha(prior_context_path)==prior_inputs['frozen_inputs']['context.json'] and
            sha(prior_paid_path)==prior_inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(prior_paid['rows'])==264 and prior_paid['rows']==prior_context['exact_paid_bodies'] and
            prior_paid['old_compilations']==prior_paid['copies']==prior_context['old_objects_copied']==0 and
            context['goldbach_closure_graft']==prior_context['goldbach_closure_graft'] and
            sha(exact(context['goldbach_closure_graft']))==prior_inputs['frozen_inputs']['goldbach-closure-graft.json']==
                inputs['frozen_inputs']['goldbach-closure-graft.json'],
            'CP741 signed parent facts or prior Goldbach graph evidence drift')
    for current,old in zip(rows[:264],prior_paid['rows'],strict=True):
        module = current['module']
        artifact = selected(module,roots)[0]
        require(current=={**old,'object':current['object'],'provider':current['provider']} and
                all(artifact.samefile(p) for p in (current['object'],current['provider'],old['object'],old['provider'])) and
                sha(artifact)==old['object_sha256'] and sha(repo/old['main'])==old['source_sha256'],
                'CP742 inherited CP741 exact binding drift '+module)

    promotion = read(promotion_path)
    require(promotion['exact'] and promotion['old_compilations']==0 and
            promotion['stage_map_sha256']==sha(prior_stage_path) and len(promotion['inputs'])==len(prior_stage['inputs'])==4,
            'CP741 exact promotion scope drift')
    for row,owner,promoted,ending,attempt in zip(rows[264:],prior_stage['inputs'],promotion['inputs'],
            ('Tower','CoherentFibre','CoherentLift','Completion'),
            ('001','002','003','001'),strict=True):
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
                'CP741 exact source, strict compile and selected inode drift '+module)
    verify_inherited_kummer_graft(context,prior_context,inputs,prior_inputs,roots,read(exact(stage['construction_cost'])))
    mathlib = read(exact(context['mathlib_bindings']))['rows']
    require(len(mathlib)==16 and mathlib[:15]==read(exact(prior_context['mathlib_bindings']))['rows'] and
            all(selected(row['module'],roots)[0].samefile(exact(row['object'])) and exact(row['source']).is_file() for row in mathlib),
            'CP742 exact Mathlib provider drift')
    noetherian = mathlib[-1]
    mathlib_root = repo/'Lean/.lake/packages/mathlib'
    mathlib_source = exact(noetherian['source'])
    require(noetherian['module']=='Mathlib.RingTheory.Noetherian.Basic' and
            mathlib_source==mathlib_root/'Mathlib/RingTheory/Noetherian/Basic.lean' and
            noetherian['tracked_source_commit']=='db584cd6d46c92f209a44c0f1c829460d327499d' and
            tracked_source_sha(mathlib_root,noetherian['tracked_source_commit'],mathlib_source)==noetherian['source']['sha256'] and
            selected(noetherian['module'],roots)[0].samefile(noetherian['provider']),
            'CP742 direct Noetherian source commit or object drift')
    require(sum(row['binding_kind']!='exact-certified-source-reuse' for row in rows)==82,
            'CP742 exact legacy parent count drift')
    direct = []
    for ending in ('.Cofinal.Topology.CokernelTorsion.Tower','.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.Completion'):
        module, = [row['module'] for row in rows if row['module'].endswith(ending)]
        direct.append(module)
    return paid,direct,noetherian['module']

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
    require(len(science)==3 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'CoherentKernel','Noetherian','CompletionExact'} and
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
    paid,direct,mathlib_direct=verify_kummer_coherent_kernel_parents(args.repo,package,inputs,stage,context,roots)
    imports={m for row in science.values() for m in row['base']} - science.keys()
    require(imports==set(inputs['audit_base']),'CP742 exact direct import scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    parent_view=base.parent/'iqa-cofinal-torsion-completion/lean-path.txt'
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
    require(imports==set(direct)|{mathlib_direct},'CP742 exact production import drift')
    gate_imports=re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)
    paid_model, = [row['module'] for row in paid['rows']
                   if row['role']=='CP739 exact PaidCokernelModel']
    require(gate_imports==[inputs['entry'],paid_model] and paid_model not in imports,
            'CP742 independent original R model Gate-only import drift')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='cofinal-torsion-kernel-compiler-companions/v1' and
            companions['companions']==inputs['compiler_companions']==[],
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
            report['fresh_raw_regions'] == 3 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    expected_runtime = [{'name':r['name'],'owner':r['module'],'safe_source':r['owner'],
        'isUnsafe':False,'isPartial':True,'self_edges':1,'nonself_incoming_edges':0,
        'type_preserved':True,'value_preserved':True} for r in inputs['compiler_companions']]
    require(len(expected_runtime)==counts['compiler_runtime']==0 and
            sorted(expected_runtime,key=lambda r:r['name'])==sorted(stage['compiler_runtime'],key=lambda r:r['name']),
            'exact compiler companion CI or logical separation drift')
    require(counts['raw_private']==counts['private']==11, 'private logical scope drift')
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
    generic = ['L','M','_','_']
    evaluated = generic+['evaluate','injective','p']
    noetherian = generic+['_','evaluate','injective','p']
    public = {
        'torsion_restriction_power': (['M','_','p','j','d','value'],0),
        'primePowerTorsionLimitMap': (generic+['move','p'],0),
        'torsion_limit_map_restriction': (generic+['move','p','j','value'],0),
        'ambientToCokernelAtLimit': (generic+['evaluate','p'],0),
        'cokernel_connecting_limit_kernel_of_bounded': (evaluated+['d','bounded'],0),
        'ambient_to_cokernel_limit_injective_of_bounded': (evaluated+['d','bounded'],0),
        'source_prime_torsion_bounded': (['L','_','_','p'],0),
        'cokernel_connecting_limit_kernel': (noetherian,0),
        'ambient_to_cokernel_limit_injective': (noetherian,0),
        'actual_kummer_completion_kernel': (['source','p'],0),
        'actual_kummer_completion_class_fibre': (['source','p','left','right'],0),
    }
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'bounded source torsion and original Kummer class fibre telescope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==counts['safe']==24 and
            stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and
            counts['inductive_generated_CIs']==0,'full fresh logical CI coverage drift')
    ancestry = report['kummer_coherent_kernel_data_ancestry']
    require(ancestry==inputs['kummer_coherent_kernel_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'bounded source correction and original coherent Kummer class fibre ancestry drift')
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
    save(output/'provenance.json',{'schema':'cp742-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
         'paid_direct_imports':3,'paid_project_imports':2,'gate_only_project_imports':1,'pinned_mathlib_imports':1,'new_mathlib_support_bindings':1,'inherited_mathlib_support_bindings':15,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':268,'legacy_project_bindings':82,'inherited_parent_references':264,'added_paid_parent_rows':4,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None, 'paid_direct_imports':3,'paid_project_imports':2,'gate_only_project_imports':1,'pinned_mathlib_imports':1,'new_mathlib_support_bindings':1,'inherited_mathlib_support_bindings':15,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':268,'legacy_project_bindings':82,'inherited_parent_references':264,'added_paid_parent_rows':4,'rational_kummer_cached_project_modules':29,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp742-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP742_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp742-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
