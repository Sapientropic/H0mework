#!/usr/bin/env python3
"""Verify the original stored material timeline and fixed-target actor consumers."""
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


def verify_cp597(repo, row, hit):
    module = row['module']
    require(row['binding_kind']=='exact-certified-source-reuse' and module.endswith((
        '.GenericFoundation.Operations.Runtime.StoredHistory',
        '.History.Inventory.SourceSelected.Calculation.Cursor.Stored')), 'unexpected CP597 provider '+module)
    manifest_path, cert_path, promotion_path, stage_path, receipt_path = map(exact,row['bindings'])
    manifest, cert, promotion, stage, receipt = map(read,
        (manifest_path, cert_path, promotion_path, stage_path, receipt_path))
    package = repo/'Verification/no-island/goldbach-stored-micro-actor'
    inputs_path = package/'inputs.json'
    inputs = read(inputs_path)
    revision = row['tracked_source_commit']
    require(manifest_path==package/'manifest.json' and cert_path==package/'certificate.json' and
            manifest['checkpoint']==cert['checkpoint']=='CP597' and cert['verdict']=='certified' and
            set(cert['axioms'])=={'propext','Classical.choice','Quot.sound'}, 'CP597 certificate identity drift')
    for path in (manifest_path,cert_path,inputs_path,repo/row['main']):
        blob = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
            revision+':'+path.relative_to(repo).as_posix()], cwd=repo)
        require(hashlib.sha256(blob).hexdigest()==sha(path), 'CP597 tracked bytes drift '+str(path))
    for path in (cert_path,inputs_path):
        entry, = [r for r in manifest['members'] if r['path']==path.name]
        require(entry['sha256']==sha(path) and entry['bytes']==path.stat().st_size,
            'CP597 manifest binding drift '+str(path))
    require(cert['inputs']['sha256']==sha(inputs_path) and cert['inputs']['bytes']==inputs_path.stat().st_size and
            cert['main_promotion']['sha256']==sha(promotion_path) and
            cert['main_promotion']['bytes']==promotion_path.stat().st_size and
            inputs['frozen_inputs']['stage-map.json']==sha(stage_path)==promotion['stage_map_sha256'] and
            stage['frozen'] and promotion['exact'] and promotion['old_compilations']==0,
            'CP597 promotion / stage drift')
    final, = [r for r in stage['inputs'] if r['module']==module]
    promoted, = [r for r in promotion['inputs'] if r['module']==module]
    authority = exact(row['authority_object'])
    require(final['main']==promoted['main']==row['main'] and
            final['source_sha256']==promoted['source_sha256']==row['source_sha256']==sha(repo/row['main']) and
            Path(final['source'])==Path(receipt['source']) and
            sha(receipt['source_snapshot'])==receipt['source_sha256']==row['source_sha256'] and
            exact(final['receipt'])==receipt_path and promoted['receipt_sha256']==sha(receipt_path) and
            final['final_attempt']==receipt['attempt']=='003' and
            receipt['command']==final['strict_command'] and receipt['exit_code']==0 and
            receipt['source_unchanged'] and receipt['old_compilations']==0 and
            {'--trust=0','-DElab.async=false','-DwarningAsError=true'}<=set(receipt['command']),
            'CP597 strict/source binding drift '+module)
    require(all(hit.samefile(path) for path in
                (authority,row['object'],row['provider'],exact(final['object']),exact(receipt['object']))) and
            sha(hit)==row['object_sha256']==promoted['object_sha256']==final['object']['sha256'],
            'CP597 selected object drift '+module)


def verify_native_codegen(base, stage):
    cost = read(exact(stage['construction_cost']))
    report_path = base/'codegen-verification.json'
    report = read(report_path)
    require(report==cost['native_codegen'], 'generated C record differs from frozen construction cost')
    module = 'SaturationMonoid.GenericFoundation.Operations.Runtime.StoredTimeline'
    owner, = [row for row in stage['inputs'] if row['module']==module]
    receipt = read(exact(owner['receipt']))
    command = receipt['command']
    source = exact(report['source'])
    require(owner['final_attempt']=='003' and receipt['exit_code']==0 and receipt['source_unchanged'] and
            command==owner['strict_command'] and command[command.index('-c')+1]==str(source) and
            command[command.index('-o')+1]==owner['object']['path'] and
            source==base/'objects/StoredTimeline-003.c',
            'C and OLean do not share the selected strict invocation')
    raw = source.read_text()
    require(raw.splitlines()[1]=='// Module: '+module, 'generated C module identity drift')
    headers = list(re.finditer(r'^LEAN_EXPORT [^\n;]*? (\w+)\(([^;\n]*)\)\{\n',raw,re.M))
    functions = {m[1]:(re.findall(r'lean_object\* (v_\w+_)',m[2]),
                     raw[m.end():headers[i+1].start()] if i+1<len(headers) else raw[m.end():])
                 for i,m in enumerate(headers)}

    def function(suffix):
        hit, = [record for name,record in functions.items() if name.endswith(suffix)]
        require(not re.search(r'\b\w*(?:successor|nextState|generateHistory|storedPairAt|stored_pair_run)\w*\(',
                              hit[1]), 'generated history recomputation in '+suffix)
        return hit

    def assigned(body, expression):
        hits = re.findall(r'^(v_(?!unused_)\w+_) = '+expression+r';$',body,re.M)
        require(len(hits)==1, 'expected exact generated assignment '+expression)
        return hits[0]

    def get_field(body, obj, field):
        return assigned(body,rf'lean_ctor_get\({obj}, {field}\)')

    (project,cursor),step = function('_collectStep___redArg')
    state = get_field(step,cursor,0)
    pair = get_field(step,cursor,1)
    tail = get_field(step,get_field(step,pair,0),2)
    acc = get_field(step,pair,1)
    next_state = assigned(step,rf'\w+_storedHead___redArg\({tail}\)')
    material = assigned(step,rf'lean_apply_1\({project}, {state}\)')
    pushed = assigned(step,rf'lean_array_push\({acc}, {material}\)')
    branches = re.findall(r'lean_ctor_set\((v_\w+_), ([01]), (v_\w+_)\);',step)
    tail_pairs = [obj for obj,index,value in branches if index=='0' and value==tail]
    next_pairs = [obj for obj,index,value in branches if index=='0' and value==next_state]
    joined, = set(value for obj,index,value in branches if index=='1' and obj in next_pairs)
    require(len(tail_pairs)==len(next_pairs)==2 and
            all((obj,'1',pushed) in branches and f'{joined} = {obj};' in step for obj in tail_pairs) and
            step.count('lean_apply_1(')==step.count('lean_array_push(')==1,
            'fold step loses the stored tail or performs additional work')

    (_,_,fold_project,fold_fuel,fold_cursor),fold = function('_collect_spec__0___redArg')
    (loop_project,loop_fuel,loop_cursor),loop = function('_collect_spec__0_spec__0___redArg')

    def decrease(body, fuel, initial, projector):
        one = assigned(body,r'lean_unsigned_to_nat\(1u\)')
        remain = assigned(body,rf'lean_nat_sub\({fuel}, {one}\)')
        updated = assigned(body,rf'\w+_collectStep___redArg\({projector}, {initial}\)')
        require(f'return {initial};' in body and body.count('_collectStep___redArg(')==1,
                'generated fold does not preserve the zero-fuel cursor')
        return remain,updated

    remain,updated = decrease(fold,fold_fuel,fold_cursor,fold_project)
    folded = assigned(fold,rf'\w+_collect_spec__0_spec__0___redArg\({fold_project}, {remain}, {updated}\)')
    require(f'return {folded};' in fold,'fold does not return the specialized tail loop')
    remain,updated = decrease(loop,loop_fuel,loop_cursor,loop_project)
    require(f'{loop_fuel} = {remain};\n{loop_cursor} = {updated};\ngoto _start;' in loop and
            loop.count('goto _start;')==1,'specialized loop does not thread its retained cursor')

    (world,process,project,fuel,state,history,acc),collect = function('_collect___redArg')
    inner, = re.findall(rf'lean_ctor_set\((v_\w+_), 0, {history}\);',collect)
    outer, = re.findall(rf'lean_ctor_set\((v_\w+_), 0, {state}\);',collect)
    require(f'lean_ctor_set({inner}, 1, {acc});' in collect and
            f'lean_ctor_set({outer}, 1, {inner});' in collect,'fold loses its initial stored cursor')
    final = assigned(collect,rf'\w+_collect_spec__0___redArg\({world}, {process}, {project}, {fuel}, {outer}\)')
    material = assigned(collect,rf'lean_apply_1\({project}, {get_field(collect,final,0)}\)')
    final_array = get_field(collect,get_field(collect,final,1),1)
    result = assigned(collect,rf'lean_array_push\({final_array}, {material}\)')
    require(f'return {result};' in collect and collect.count('lean_apply_1(')==collect.count('lean_array_push(')==1,
            'final state is not projected and appended exactly once')

    (world,process,project,fuel,history),entry = function('_storedTimeline___redArg')
    one = assigned(entry,r'lean_unsigned_to_nat\(1u\)')
    capacity = assigned(entry,rf'lean_nat_add\({fuel}, {one}\)')
    root = assigned(entry,rf'\w+_storedHead___redArg\({history}\)')
    empty = assigned(entry,rf'lean_mk_empty_array_with_capacity\({capacity}\)')
    result = assigned(entry,rf'\w+_collect___redArg\({world}, {process}, {project}, {fuel}, {root}, {history}, {empty}\)')
    require(f'return {result};' in entry,'collector does not start at the original stored head')

    (group,env,table,index),read_env = function('_timelineEnvironments___redArg')
    sub = get_field(read_env,group,2)
    old = assigned(read_env,rf'lean_array_fget_borrowed\({table}, {index}\)')
    next_index = assigned(read_env,rf'l_Fin_succ___redArg\({index}\)')
    new = assigned(read_env,rf'lean_array_fget_borrowed\({table}, {next_index}\)')
    delta = assigned(read_env,rf'lean_apply_2\({sub}, {new}, {old}\)')
    old_env = assigned(read_env,rf'lean_apply_1\({env}, {old}\)')
    delta_env = assigned(read_env,rf'lean_apply_1\({env}, {delta}\)')
    require(read_env.count('lean_array_fget_borrowed(')==2 and
            re.search(rf'lean_ctor_set\((v_\w+_), 0, {old_env}\);\nlean_ctor_set\(\1, 1, {delta_env}\);\nreturn \1;',
                      read_env), 'lookup must read adjacent cells of one array and preserve new minus old')
    expected = {'stored_root_field':True,'stored_tail_field':True,'old_successor_calls':0,
        'preallocated_capacity':'fuel+1','tail_loop':True,'material_projections_per_state':1,
        'pushes_per_state':1,'adjacent_array_reads':2,'same_table':True,'effect':'new minus old'}
    require(report=={'source':report['source'],**expected},'frozen generated C claim drift')
    return {'report_sha256':sha(report_path),'c_sha256':sha(source),**expected,'old_history_lookup_calls':0}


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
                          ('raw_inventory_receipt','receipts/RawInventory-002.receipt.json')):
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
        require(module.startswith('SaturationMonoid.') and module.endswith(('.GenericFoundation.Operations.Runtime.StoredTimeline','.History.Inventory.SourceSelected.Calculation.Cursor.Timeline')) and
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
    require(paid['schema']=='stored-actor-timeline-paid-parents/v1' and
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
        verify_cp597(args.repo,row,hit)
    native = verify_native_codegen(base,stage)
    require(native==inputs['native_codegen'] and
            native['report_sha256']==inputs['frozen_inputs']['codegen-verification.json'],
            'independently checked native timeline evidence drift')
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
    projection = ['N','process','A','project','fuel','state','history']
    env_read = ['environment','fuel','table','i']
    env_actual = ['environment','readMaterial','runtime','fuel','history','i']
    public = {
        'storedTimeline':projection,
        'stored_timeline_adjacent':projection+['i'],
        'timelineEnvironments':env_read,
        'timelineInventory':env_read,
        'timeline_environments_actual':env_actual,
        'timeline_inventory_actual':env_actual,
        'fullTable':['depth'],
        'sourceReadout':['depth'],
        'source_readout_pulse':['depth','i'],
        'pulseInventory':['depth','i'],
        'pulse_inventory_actual':['depth','i'],
        'source_character_from_full':['depth','bound','within','word','i'],
        'source_readout_terminal':['depth'],
    }
    generic_env = {'timelineEnvironments','timelineInventory','timeline_environments_actual','timeline_inventory_actual'}
    for name in generic_env:
        binders[name] = binders[name][-len(public[name]):]
    require(binders==public, 'stored timeline or fixed-target consumer input drift')
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
    save(output/'provenance.json',{'schema':'cp598-provenance/v1','science':actual,
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
        save(cost,{'schema':'cp598-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP598_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp598-stored-actor-timeline','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp598-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
