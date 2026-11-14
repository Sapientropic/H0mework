#!/usr/bin/env python3
"""Verify the original sparse price schedule, one appended actual read, and graph and relation writeback."""
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


def verify_parent(args, roots, row):
    module = row['module']
    source = args.repo/row['main']
    hit,_ = selected(module,roots)
    require(hit.samefile(row['object']) and hit.samefile(row['provider']) and
            sha(hit)==row['object_sha256'] and sha(source)==row['source_sha256'],
            'paid exact source/body drift '+module)
    binding_path,cert_path,receipt_path = [exact(row[key]) for key in ('signed_binding','certificate','receipt')]
    binding,cert,receipt = [read(path) for path in (binding_path,cert_path,receipt_path)]
    if module=='SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection':
        old, = [item for item in binding['owned_sources'] if item['module']==module]
        require(binding['checkpoint']=='CP476' and binding['machine_finalized'] and binding['current_finalized'] and
                exact(binding['independent_certificate']).samefile(cert_path) and cert['verdict']=='PASS' and
                set(cert['standard_axioms'])==AXIOMS and cert['old_CI_or_getter_replays']==0 and
                cert['heavy_released'] and binding['frozen_capsule']==cert['frozen_capsule'] and
                old['repoPath']==row['main'] and source.samefile(old['destination']) and
                old['new_sha256']==old['source']['sha256']==old['frozen_source']['sha256']==row['source_sha256'] and
                exact(old['receipt']).samefile(receipt_path) and exact(old['object']).samefile(hit) and
                old['object']['sha256']==row['object_sha256'] and receipt['object']==old['object'] and
                receipt['module']==module and receipt['source']['sha256']==row['source_sha256'] and
                receipt['strict_green'] and receipt['exit_code']==receipt['parent_recompile']==
                receipt['parent_copies']==receipt['Scope_runs']==0 and set(FLAGS[:3])<=set(receipt['command']),
                'original CP476 finite Gram source, object, or certificate drift')
        return

    require(module.endswith('.BornPriceWriteback'),'unexpected signed source parent '+module)
    checkpoint = 'CP589'
    old = verify_signed_science(args,roots,binding_path,cert_path,checkpoint,module)
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
                          ('raw_inventory_receipt','receipts/RawInventory-002.receipt.json')):
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
        require(module.startswith('SaturationMonoid.') and module.endswith(('.GenericFoundation.Scalar.Feature.FiniteGram.CofinalInsertion','.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord',
                    '.GammaSource.PositionGap.CofinalPriceRecord')) and
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
    require(paid['schema']=='cofinal-sparse-record-paid-parents/v1' and
            len(parents)==2 and parents==context['exact_paid_bodies'] and
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
        verify_parent(args,roots,row)
    for ancestor in inputs['gate_signed_science']:
        verify_signed_science(args,roots,exact(ancestor['stage_map']),exact(ancestor['certificate']),
                              ancestor['checkpoint'],ancestor['module'])
    gate = inputs['gate_ancestor']
    cert_path = exact(gate['certificate'])
    signed = read(cert_path)
    prior_path = cert_path.with_name('inputs.json')
    prior = read(prior_path)
    paid_path = exact(gate['paid_binding'])
    require(signed['checkpoint']=='CP557' and signed['verdict']=='certified' and set(signed['axioms'])==AXIOMS and
            signed['inputs']['sha256']==sha(prior_path) and
            prior['frozen_inputs']['paid-parent-bindings.json']==sha(paid_path) and
            prior['local_evidence_sha256']['evidence/paid-parents.json']==sha(paid_path),
            'original same-root whole provenance drift')
    whole, = [r for r in read(paid_path)['rows'] if r['module']==gate['module']]
    hit,_ = selected(whole['module'],roots)
    require(whole['module'].endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction') and
            hit.samefile(whole['object']) and hit.samefile(whole['provider']) and
            sha(hit)==whole['object_sha256'] and sha(args.repo/whole['main'])==whole['source_sha256'],
            'original same-root whole/next selected body drift')
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
            report['fresh_raw_regions'] == 3 and report['paid_base_environment_imports'] == 1 and
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
    literal_frame = ['observation','nontrivial','half','depth','start']
    scalar_frame = ['source','n']
    recursion = ['source','separates']
    expected = {
        'Values':['n'],
        'sample':['n','rows','field'],
        'columns':[*scalar_frame,'rows','j'],
        'replay':[*scalar_frame,'a','time'],
        'withBirth':[*scalar_frame,'a','b','time'],
        'priorFit':[*scalar_frame,'rows'],
        'birthResidual':[*scalar_frame,'rows','time'],
        'exists_birth_pivot':[*scalar_frame,'rows','cutoff','separates'],
        'decodeInsert':[*scalar_frame,'rows','time','previous','current'],
        'decode_insert_exact':[*scalar_frame,'rows','faithful','time','pivot','a','b'],
        'Schedule':['source','count'],
        'pivotTime':[*recursion,'n','rows'],
        'pivot_nonzero':[*recursion,'n','rows'],
        'prior_lt_pivot':[*recursion,'n','rows','i'],
        'appendSchedule':[*recursion,'n','prior'],
        'schedule':[*recursion,'count'],
        'schedule_prior':[*recursion,'count','i'],
        'schedule_last':[*recursion,'count'],
        'schedule_fresh':[*recursion,'count','i'],
        'schedule_read_insert':[*recursion,'n','a','b'],
        'priceSchedule':[*literal_frame,'count'],
        'nativePriceAt':['observation','half','field','time'],
        'recordedPrices':[*literal_frame,'count','field'],
        'actual_price_record_prior':[*literal_frame,'count','field','i'],
        'actual_price_record_fresh':[*literal_frame,'count','i'],
        'decodeRecordedPrices':[*literal_frame,'count','previous','latest'],
        'actual_recorded_price_birth':[*literal_frame,'count','a','b'],
        'actual_sparse_price_writeback':[*literal_frame,'ordinal','a','b'],
    }
    require(binders==expected,'actual pivot, preserved address or original price read input drift')
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
    save(output/'provenance.json',{'schema':'cp590-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':2,'gate_ancestor_bindings':2,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':2,'gate_ancestor_bindings':2,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp590-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP590_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp590-cofinal-sparse-record','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp590-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
