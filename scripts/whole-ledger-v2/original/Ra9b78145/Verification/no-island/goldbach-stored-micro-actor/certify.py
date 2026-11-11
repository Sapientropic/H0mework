#!/usr/bin/env python3
"""Verify the stored adjacent micro states and the original fixed-target actor consumers."""
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


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def exact(record, root=Path('.')):
    path = root/record['path']
    require(('bytes' not in record or path.stat().st_size==record['bytes']) and sha(path)==record['sha256'],'exact file drift '+str(path))
    return path


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    with Path(path).open('w') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def selected(module, roots):
    package = module.split('.')[0]
    for index, root in enumerate(roots):
        if (root/package).is_dir() or (root/(package+'.olean')).is_file():
            path = root/(module.replace('.', '/')+'.olean')
            require(path.is_file(), 'selected package root lacks '+module)
            return path, index
    raise RuntimeError('missing '+module)


def verify_cp74(repo, row, hit):
    module = row['module']
    prefix = module=='SaturationMonoid.GenericFoundation.Operations.Runtime.Prefix'
    require(row['binding_kind']=='exact-tracked-closure-reuse' and
            (prefix or module.endswith('.History.Inventory.SourceSelected.Calculation.Cursor.Consumer')),
            'unexpected CP74 provider '+module)
    manifest_path, verdict_path = map(exact,row['bindings'])
    manifest, verdict = map(read,(manifest_path,verdict_path))
    revision = row['tracked_source_commit']
    trust = verdict['trust']
    flags = trust['flags']
    require(verdict['checkpoint']=='CP74' and verdict['verdict']=='certified' and
            verdict['fixed_head']==manifest['head']==revision and
            trust['manifest']['sha256']==sha(manifest_path) and
            Path(trust['manifest']['path']).name==manifest_path.name and
            verdict['capsule']['sha256']==manifest['capsule_sha256'] and
            set(verdict['axioms']['allowed_only'])=={'propext','Classical.choice','Quot.sound'} and
            flags[flags.index('-t')+1]=='0' and '-DwarningAsError=true' in flags and
            verdict['prior_binding']['final_shared_source_import_and_artifact_equal'] and
            not manifest['formal_prior_binding_requires_rebuild'], 'CP74 exact verdict/manifest drift')
    frozen = manifest['closure'][module]
    relative_source = Path(row['main']).relative_to('Lean')
    old_source = manifest_path.parent/'src'/relative_source
    require(frozen['repository_path']==row['main'] and frozen['sha256']==row['source_sha256'] and
            frozen['owner']=='HEAD' and frozen['worktree_matches'] and
            Path(frozen['source'])==Path('runtime/cp74-independent-clean/src')/relative_source and
            sha(old_source)==row['source_sha256'], 'CP74 source closure drift '+module)
    blob = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',revision+':'+row['main']],cwd=repo)
    require(hashlib.sha256(blob).hexdigest()==row['source_sha256']==sha(repo/row['main']),
            'tracked CP74 source bytes drift '+module)
    authority = exact(row['authority_object'])
    relative_artifact = relative_source.with_suffix('.olean')
    reuse, = [r for r in manifest['reuse_artifacts'][module]
              if Path(r['snapshot'])==Path('runtime/cp74-independent-clean/lib')/relative_artifact]
    require(authority==manifest_path.parent/'lib'/relative_artifact and
            hit.samefile(row['object']) and hit.samefile(row['provider']) and
            hit.samefile(authority)==(not prefix) and
            sha(hit)==reuse['sha256']==row['authority_object']['sha256']==row['object_sha256'] and
            hit.stat().st_size==row['authority_object']['bytes'],
            'CP74 selected versus authority artifact drift '+module)


def verify_native_codegen(base, stage):
    cost = read(exact(stage['construction_cost']))
    report_path = base/'codegen-verification.json'
    report = read(report_path)
    require(report==cost['native_codegen'], 'generated C record differs from frozen construction cost')
    module = 'SaturationMonoid.GenericFoundation.Operations.Runtime.StoredHistory'
    selected, = [row for row in stage['inputs'] if row['module']==module]
    receipt = read(exact(selected['receipt']))
    command = receipt['command']
    source = exact(report['source'])
    require(selected['final_attempt']=='003' and receipt['exit_code']==0 and receipt['source_unchanged'] and
            command[command.index('-c')+1]==str(source) and
            command[command.index('-o')+1]==selected['object']['path'] and
            source==base/'objects/StoredHistory-003.c',
            'selected OLean and generated C were not emitted by the same strict invocation')
    raw = source.read_text()
    require(raw.splitlines()[1]=='// Module: '+module, 'generated C module identity drift')
    headers = list(re.finditer(r'^LEAN_EXPORT [^\n;]*? (\w+)\(([^;\n]*)\)\{\n',raw,re.M))
    functions = {m[1]:(m[2],raw[m.end():headers[i+1].start()] if i+1<len(headers) else raw[m.end():])
                 for i,m in enumerate(headers)}
    _,stored = next(value for name,value in functions.items() if name.endswith('_storedHead___redArg'))
    parameters,branch = next(value for name,value in functions.items()
                             if name.endswith('_storedPairAt___redArg___lam__1'))
    require(not re.search(r'\b\w*(?:successor|nextState|generateHistory)\w*\(',branch+stored),
            'generated stored-pair path computes an old successor')
    fields = re.findall(r'(\w+) = lean_ctor_get\((\w+), ([01])\);',stored)
    require(len(fields)==2 and fields[0][1]==fields[1][1] and {row[2] for row in fields}=={'0','1'} and
            all(f'return {row[0]};' in stored for row in fields) and 'lean_obj_tag' in stored,
            'storedHead does not return each history constructor state directly')
    tail_read = re.search(r'(\w+) = lean_ctor_get\((v_history_\d+_), 2\);',branch)
    next_read = re.search(r'(\w+) = \w+_storedHead___redArg\((\w+)\);',branch)
    require(tail_read is not None and next_read is not None and tail_read[1]==next_read[2],
            'right state is not the head of the actual stored tail')
    pair = re.search(r'(\w+) = lean_alloc_ctor\(0, 2, 0\);',branch)
    old_state = re.search(r'\b(v_state_\d+_)\b',parameters)
    require(pair is not None and old_state is not None and
            f'lean_ctor_set({pair[1]}, 0, {old_state[1]});' in branch and
            f'lean_ctor_set({pair[1]}, 1, {next_read[1]});' in branch,
            'emitted pair does not have the actual stored adjacent states')
    recurse = re.search(r'(\w+) = lean_apply_2\((v_previous_\d+_), (\w+), (\w+)\);',branch)
    require(recurse is not None and (recurse[3],recurse[4])==(next_read[1],tail_read[1]) and
            f'l_Fin_cases___redArg({pair[1]}, {recurse[1]},' in branch, 'lookup recursion does not reuse the exact tail')
    require(report['stored_tail_state'] and report['old_current_parameter'] and report['actual_adjacent_pair'] and
            report['old_successor_calls']==0, 'frozen generated C verification scope drift')
    return {'report_sha256':sha(report_path),'c_sha256':report['source']['sha256'],'old_successor_calls':0,
            'stored_pair_and_tail_reuse_checked':True,'stored_head_fields_checked':2}


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
    require(len(science)==2 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.endswith(('.GenericFoundation.Operations.Runtime.StoredHistory','.History.Inventory.SourceSelected.Calculation.Cursor.Stored')) and
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
                set(FLAGS[:3]) <= set(actual_receipt['command']) and actual_receipt['old_compilations']==0,
                'strict source/body receipt drift '+module)
        science_actual.append({**row,'selected_olean':str(artifact),'search_path_index':index})

    paid_path = package/'evidence/paid-parents.json'
    paid = read(paid_path)
    parents = paid['rows']
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(paid['schema']=='micro-history-actor-read-paid-parents/v1' and
            len(parents)==2 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base'])=={row['module'] for row in parents}, 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    require(output['schema']=='owned-proof-stage-output-location/v1' and Path(output['logical'])==base and
            physical.is_relative_to('runtime/ and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','source-root','receipts')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' for row in frozen.values()),
            'second SSD output binding drift')
    for row in parents:
        hit,_ = selected(row['module'],roots)
        verify_cp74(args.repo,row,hit)
    native = verify_native_codegen(base,stage)
    require(native==inputs['native_codegen'] and
            native['report_sha256']==inputs['frozen_inputs']['codegen-verification.json'],
            'independently checked native stored-pair evidence drift')
    require(read(exact(stage['compiler_companions']))['companions']==[], 'unexpected compiler runtime companions')
    return inputs,roots,science_actual


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['duplicates'] == 0 and
            stage['inherited'] == counts['inherited'] == report['inherited_generated_full_CI_matches'] and
            stage['fresh_replayed'] == counts['kernel_calls'] == report['fresh_safe_replayed_CIs'] and
            stage['fresh_replayed']+stage['inherited']==stage['raw'] and
            not stage['base_has_unverified_sources'] and not stage['compiler_runtime'] and
            report['fresh_raw_regions'] == 2 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    owners = {r['module']:r for r in actual}
    for owner in stage['modules']:
        selected_owner = owners.pop(owner['module'])
        require(sha(owner['selected_olean']) == selected_owner['artifact_sha256'] and
                owner['raw'] == selected_owner['raw_CIs'] and owner['imports'] == selected_owner['raw_imports'] and
                owner['compiler_extras'] == selected_owner['compiler_extras'],
                'wrong audited owner '+owner['module'])
    require([r['name'] for r in stage['inherited_generated_full_CIs']]==inputs['inherited_generated_CIs'] and
            all(r['same_full_constant_info'] and not r['kernel_replayed']
                for r in stage['inherited_generated_full_CIs']), 'inherited CI qualification drift')
    require(not owners and report['safe_private_original_CIs'] == stage['raw'] == counts['safe'] and
            stage['kernel_calls'] == counts['kernel_calls'] and stage['compiler_extras'] == counts['extras'] and
            sum(r['name'].startswith('_private.') for r in stage['declarations']) == counts['private'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['source_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source provenance')
    binders = {r['name'].rsplit('.',1)[-1]:r['binders'] for r in report['public_mouths']}
    pair = ['N','process','runtime','fuel','history','i']
    env_frame = ['readMaterial','environment','runtime','fuel','history','i']
    expected = {
        'storedPairAt':['N','process','fuel','state','history','a._@._internal._hyg.0'],
        'stored_pair_actual':pair,
        'storedActivation':pair,
        'stored_activation_actual':pair,
        'stored_successor_actual':pair,
        'storedOldEnvironment':env_frame,
        'storedIncrementEnvironment':env_frame,
        'stored_environments_actual':env_frame,
        'storedStageInventory':env_frame,
        'stored_inventory_actual':env_frame,
        'budget':['depth'],
        'fullHistory':['depth'],
        'stored_seed_material':['depth'],
        'stored_actor_prefix':['depth','count','within'],
        'stored_actor_increment':['depth','count','within'],
        'stored_whole_and_next':['depth','i'],
        'stored_character_actual':['depth','bound','word','stage'],
        'stored_first_cochain':['depth'],
        'storedFinal':['depth'],
        'stored_final_value':['depth'],
        'stored_consumes_original_disposition':['depth'],
    }
    generic_env = {'storedOldEnvironment','storedIncrementEnvironment','stored_environments_actual',
        'storedStageInventory','stored_inventory_actual'}
    for name in generic_env:
        binders[name] = binders[name][-len(env_frame):]
    require(binders==expected, 'stored micro-history or fixed-target consumer input drift')
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
    save(output/'provenance.json',{'schema':'cp597-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':2,'gate_ancestor_bindings':0,'verification_overlay_objects':0,'native_codegen':inputs['native_codegen'],'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':2,'gate_ancestor_bindings':0,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp597-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP597_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp597-stored-micro-actor','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp597-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
