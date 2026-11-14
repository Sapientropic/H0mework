#!/usr/bin/env python3
"""Verify the actual scheduled native receipts, fixed Fourier prices, and both stock successors."""
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


def verify_signed_science(args, roots, stage_path, cert_path, checkpoint, module):
    old, = [row for row in read(stage_path)['inputs'] if row['module']==module]
    signed = read(cert_path)
    prior_path = cert_path.with_name('inputs.json')
    prior = read(prior_path)
    row, = [entry for entry in prior['science'] if entry['module']==module]
    hit,_ = selected(module,roots)
    formal = old.get('main') or old['intended_formal_path']
    require(signed['checkpoint']==checkpoint and signed['verdict']=='certified' and set(signed['axioms'])==AXIOMS and
            signed['inputs']['sha256']==sha(prior_path) and
            prior['frozen_inputs']['stage-map.json']==sha(stage_path) and
            formal==row['intended_formal_path'] and
            sha(args.repo/formal)==old['source_sha256']==row['source_sha256'] and
            hit.samefile(old['object']['path']) and sha(hit)==old['object']['sha256']==row['artifact_sha256'],
            'signed selected science drift '+module)
    return old


def verify_parent(args, roots, row, whole_lineage):
    module = row['module']
    source = args.repo/row['main']
    hit, _ = selected(module, roots)
    require(hit.samefile(row['object']) and hit.samefile(row['provider']) and
            sha(hit)==row['object_sha256'] and sha(source)==row['source_sha256'],
            'paid exact source/body drift '+module)
    if row.get('binding_kind')=='exact-tracked-closure-reuse':
        if module.endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction'):
            cert541_path, paid557_path = map(exact, row['bindings'])
            cert541 = read(cert541_path)
            require(cert541['checkpoint']=='CP541' and cert541['verdict']=='certified' and
                    set(cert541['axioms'])==AXIOMS and cert541['inputs']['sha256']==sha(cert541_path.with_name('inputs.json')),
                    'original Division certificate drift')
            cert557_path = exact(whole_lineage['certificate'])
            require(whole_lineage['module']==module and whole_lineage['checkpoint']=='CP557' and
                    exact(whole_lineage['paid_binding']).samefile(paid557_path), 'original whole lineage drift')
            cert557, inputs557 = read(cert557_path), cert557_path.with_name('inputs.json')
            context557 = read(inputs557)
            require(cert557['checkpoint']=='CP557' and cert557['verdict']=='certified' and
                    set(cert557['axioms'])==AXIOMS and cert557['inputs']['sha256']==sha(inputs557) and
                    context557['frozen_inputs']['paid-parent-bindings.json']==
                    context557['local_evidence_sha256']['evidence/paid-parents.json']==sha(paid557_path),
                    'signed whole and native next binding drift')
            paid557, = [item for item in read(paid557_path)['rows'] if item['module']==module]
            require(all(paid557[k]==row[k] for k in ('module','main','source_sha256','object_sha256','provider')) and
                    hit.samefile(paid557['object']) and hit.samefile(paid557['provider']) and
                    exact(paid557['bindings'][0]).samefile(cert541_path), 'original same-root selected object drift')
            return
        require(module.endswith('.ClozelOriginalKDirectRCofinalCalculatedSource.Projection'),
                'unexpected tracked closure parent '+module)
        capsule_path, verdict_path, closure_path, receipt_path = map(exact, row['bindings'])
        capsule, verdict, closure, receipt = map(read, (capsule_path, verdict_path, closure_path, receipt_path))
        require(exact(row['receipt']).samefile(receipt_path) and
                capsule['checkpoint']==verdict['checkpoint']=='CP284' and verdict['verdict']=='certified' and
                set(verdict['authorized_axioms'])==AXIOMS and exact(verdict['candidate_capsule']).samefile(capsule_path) and
                exact(closure['candidate']).samefile(capsule_path) and
                closure['source_proof_compile_replays']==closure['Scope_replays']==closure['old_DAG_parse_replays']==0,
                'original four-branch normal receipt certificate drift')
        original, = [item for item in capsule['owned_files'] if item['module']==module]
        flags = receipt['cmd']
        require(original['repo_path']==row['main'] and original['sha256']==receipt['sha256']==row['source_sha256'] and
                original['focused_receipt_sha256']==sha(receipt_path) and Path(original['focused_receipt']).samefile(receipt_path) and
                original['focused']==receipt and receipt['module']==module and
                original['selected_olean_sha256']==receipt['olean_sha256']==row['object_sha256'] and
                hit.samefile(original['selected_olean']) and hit.samefile(receipt['olean']) and
                receipt['source_unchanged'] and receipt['actual_child_exit_collected'] and receipt['exit_code']==0 and
                receipt['ancestor_proof_AST_Scope_DAG_replayed'] is False and
                flags[flags.index('-t')+1]=='0' and set(FLAGS[1:3])<=set(flags),
                'original four-branch normal receipt selected source or object drift')
        return

    require(module.endswith('.CofinalPriceRecord'), 'unexpected signed source parent '+module)
    binding_path, cert_path, receipt_path = [exact(row[key]) for key in ('signed_binding','certificate','receipt')]
    receipt = read(receipt_path)
    old = verify_signed_science(args, roots, binding_path, cert_path, 'CP590', module)
    require(old['source_sha256']==row['source_sha256'] and old['object']['sha256']==row['object_sha256'] and
            hit.samefile(old['object']['path']) and exact(old['receipt']).samefile(receipt_path),
            'paid direct selected object or receipt drift '+module)
    require(receipt['source_unchanged'] and receipt['exit_code']==receipt['old_compilations']==0 and
            receipt['source_sha256']==row['source_sha256'] and receipt['object']['sha256']==row['object_sha256'] and
            hit.samefile(receipt['object']['path']) and set(FLAGS[:3])<=set(receipt['command']),
            'paid exact strict build drift '+module)


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
        require(module.startswith('SaturationMonoid.') and module.endswith(('.GammaSource.PositionGap.ScheduledNativePrice','.GammaSource.PositionGap.ScheduledPriceMatrix')) and
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
    require(paid['schema']=='scheduled-native-price-paid-parents/v1' and
            len(parents)==3 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base'])=={row['module'] for row in parents}, 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    entry, physical = base/'objects', Path(output['objects'])
    physical_workspace = Path(output['source_and_receipts'])
    require(Path(output['stage'])==base and output['mounted_ssd']=='Extension2' and
            entry.is_symlink() and entry.resolve()==physical.resolve() and
            physical.is_relative_to('runtime/ and physical.parent==physical_workspace and
            all((base/name).is_symlink() and (base/name).resolve()==physical_workspace/name
                for name in ('source-root','receipts')) and
            all(Path(row['object']['path']).resolve().parent==physical for row in frozen.values()),
            'second SSD output binding drift')
    for row in parents:
        verify_parent(args,roots,row,inputs['whole_lineage'])
    for ancestor in inputs['gate_signed_science']:
        verify_signed_science(args,roots,exact(ancestor['stage_map']),exact(ancestor['certificate']),
                              ancestor['checkpoint'],ancestor['module'])
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
    frame = ['observation','nontrivial','half','depth','start']
    at_row = [*frame,'count','actor','i']
    expected = {
        'scheduledMaterial':at_row,
        'actual_scheduled_material_prior':at_row,
        'paidPriceSample':at_row,
        'actual_paid_price_sample':at_row,
        'paidPriceRecord':[*frame,'count','actor'],
        'actual_paid_price_record':[*frame,'count','actor'],
        'paidMixtureRecord':[*frame,'count','samples','a','b'],
        'actual_paid_mixture_record':[*frame,'count','samples','a','b'],
        'actual_paid_birth_decode':[*frame,'count','a','b'],
        'actual_paid_price_writeback':[*frame,'ordinal','a','b'],
    }
    require(binders==expected, 'scheduled native receipt, price, or stock writeback input drift')
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
    save(output/'provenance.json',{'schema':'cp591-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':3,'gate_ancestor_bindings':1,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':3,'gate_ancestor_bindings':1,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp591-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP591_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp591-scheduled-native-price','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp591-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
