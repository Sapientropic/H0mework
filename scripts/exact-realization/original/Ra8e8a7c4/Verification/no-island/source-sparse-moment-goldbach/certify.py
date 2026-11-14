#!/usr/bin/env python3
"""Verify signed sparse moments and their use in the original Goldbach actor."""
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


def tracked_source_sha(repo, revision, path):
    blob = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
        revision+':'+path.relative_to(repo).as_posix()],cwd=repo)
    return hashlib.sha256(blob).hexdigest()


def verify_certified_owner(repo, row, hit, foundation, checkpoint, package_name, ending, attempt):
    module = row['module']
    require(row['binding_kind']=='exact-certified-source-reuse' and module.endswith(ending),
        'unexpected certified provider '+module)
    manifest_path, cert_path, promotion_path, stage_path, receipt_path = map(exact,row['bindings'])
    manifest, cert, promotion, stage, receipt = map(read,(manifest_path,cert_path,promotion_path,stage_path,receipt_path))
    package = repo/'Verification/no-island'/package_name
    inputs_path = package/'inputs.json'
    inputs = read(inputs_path)
    revision = row['tracked_source_commit']
    require(subprocess.run(['git','--no-optional-locks','merge-base','--is-ancestor',revision,foundation],
        cwd=repo).returncode==0, 'certified provider is outside the frozen foundation '+module)
    require(manifest_path==package/'manifest.json' and cert_path==package/'certificate.json' and
        manifest['checkpoint']==cert['checkpoint']==checkpoint and cert['verdict']=='certified' and
        set(cert['axioms'])=={'propext','Classical.choice','Quot.sound'},'signed parent identity drift '+module)
    source = repo/row['main']
    for path in (manifest_path,cert_path,inputs_path,source):
        require(tracked_source_sha(repo,revision,path)==sha(path)==tracked_source_sha(repo,foundation,path),
            'tracked parent evidence drift '+str(path))
    for path in (cert_path,inputs_path):
        member, = [entry for entry in manifest['members'] if entry['path']==path.name]
        require(member['sha256']==sha(path) and member['bytes']==path.stat().st_size,
            'signed parent manifest drift '+str(path))
    require(cert['inputs']['sha256']==sha(inputs_path) and cert['inputs']['bytes']==inputs_path.stat().st_size and
        cert['main_promotion']['sha256']==sha(promotion_path) and
        cert['main_promotion']['bytes']==promotion_path.stat().st_size and
        inputs['frozen_inputs']['stage-map.json']==sha(stage_path)==promotion['stage_map_sha256'] and
        stage['frozen'] and promotion['exact'] and promotion['old_compilations']==0,
        'signed parent promotion or stage drift '+module)
    final, = [entry for entry in stage['inputs'] if entry['module']==module]
    promoted, = [entry for entry in promotion['inputs'] if entry['module']==module]
    authority = exact(row['authority_object'])
    require(final['main']==promoted['main']==row['main'] and
        final['source_sha256']==promoted['source_sha256']==row['source_sha256']==sha(source) and
        Path(final['source'])==Path(receipt['source']) and
        sha(receipt['source_snapshot'])==receipt['source_sha256']==row['source_sha256'] and
        exact(final['receipt'])==receipt_path and promoted['receipt_sha256']==sha(receipt_path) and
        final['final_attempt']==receipt['attempt']==attempt and receipt['command']==final['strict_command'] and
        receipt['exit_code']==0 and receipt['source_unchanged'] and receipt['old_compilations']==0 and
        {'--trust=0','-DElab.async=false','-DwarningAsError=true'}<=set(receipt['command']),
        'signed parent strict/source binding drift '+module)
    require(all(hit.samefile(path) for path in
        (authority,row['object'],row['provider'],exact(final['object']),exact(receipt['object']))) and
        sha(hit)==row['object_sha256']==promoted['object_sha256']==final['object']['sha256'],
        'signed parent selected object drift '+module)
    return stage, inputs, cert


LOCK_NEW_COMMIT = '8634d980ddcbc1e5a273de8eb073effc358ee6b9'
LOCK_NEW_SHA = '29594f47ca4e85b19cf894013f40af6bee9a1e0e0ef51a1c846df7ca3d7379ea'
LOCK_OLD_SHA = 'aa60b347daf17a642d027cda3288f7d6f12c176c4ddd2677c28140daadb15c81'
CP605_COMMIT = '8b985de5e8f9e90c8ea526f9acc9a5e89bd48e9b'
PINS = {
    'Mathlib.LinearAlgebra.Vandermonde': 'ebe748d4855d5881103eb38aca0d5f1906363a77f72e79bed556e0b0bc2feec8',
    'Mathlib.LinearAlgebra.Matrix.Rank': '9a2d3861f260464956112d80645a1e650d4439574ddd688801975daf44e1b2e3',
    'Mathlib.Algebra.Polynomial.Roots': '282d151b6060aa84c6676a5223ee1c514bde437bf3fbf31285d32e0ff7096b47',
}
OLD_PINS = {
    'Mathlib.Algebra.BigOperators.Finsupp.Basic': '3aee7844718e1b8e2a5d0f568014a645d786b55fbe4e144f3480e547569c8d5e',
    'Batteries.Data.Fin.Lemmas': 'c062725e67bdbc314062e141284acbfdadfbf382f7e48ed32b3124bb930d3b0d',
}
REVISIONS = {
    'mathlib':'db584cd6d46c92f209a44c0f1c829460d327499d',
    'batteries':'4488d40d070b9700d4d5a6aa342f0d40c31b2a2d',
}


def lock_bytes(repo, revision):
    return subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
        revision+':Lean/lake-manifest.json'],cwd=repo)


def verify_pin(repo,row,hit,foundation,lock_commit,lock_digest,expected):
    module = row['module']
    name = 'mathlib' if module.startswith('Mathlib.') else 'batteries'
    lock = repo/'Lean/lake-manifest.json'
    binding, = row['bindings']
    require(row['binding_kind']=='pinned-'+name and module in expected and Path(binding['path'])==lock,
        'unexpected historical pin '+module)
    frozen = lock_bytes(repo,lock_commit)
    require(len(frozen)==binding['bytes'] and
        hashlib.sha256(frozen).hexdigest()==binding['sha256']==lock_digest,
        'pinned lock bytes drift '+module)
    def packages(data):
        return {entry['name']:entry for entry in json.loads(data)['packages']}
    historical = packages(frozen)
    source_foundation = packages(lock_bytes(repo,foundation))
    current = packages(lock.read_bytes())
    require(all(historical[key]==source_foundation[key]==current[key] for key in REVISIONS),
        'selected Mathlib or Batteries entry drift from source foundation')
    checkout = repo/'Lean/.lake/packages'/name
    source = Path(row['main'])
    relative = Path(*module.split('.')).with_suffix('.lean')
    revision = row['package_revision']
    head = subprocess.check_output(['git','--no-optional-locks','rev-parse','HEAD'],cwd=checkout,text=True).strip()
    require(head==historical[name]['rev']==revision==REVISIONS[name] and
        source.samefile(checkout/relative) and
        tracked_source_sha(checkout,revision,source)==sha(source)==row['source_sha256'] and
        all(hit.samefile(path) for path in (row['object'],row['provider'],checkout/'.lake/build/lib/lean'/relative.with_suffix('.olean'))) and
        sha(hit)==row['object_sha256']==expected[module],
        'pinned package source or selected object drift '+module)


def verify_old_pin(repo,row,hit,foundation):
    verify_pin(repo,row,hit,foundation,foundation,LOCK_OLD_SHA,OLD_PINS)


def verify_parent(repo,row,select,foundation):
    module = row['module']
    hit = select(module)
    require(foundation==CP605_COMMIT,'CP614 frozen source foundation drift')
    if module in PINS:
        require(subprocess.run(['git','--no-optional-locks','merge-base','--is-ancestor',foundation,LOCK_NEW_COMMIT],
            cwd=repo).returncode==0, 'pinned lock commit ancestry drift')
        verify_pin(repo,row,hit,foundation,LOCK_NEW_COMMIT,LOCK_NEW_SHA,PINS)
        return
    package_name = 'goldbach-native-action-matrix'
    stage,inputs,cert = verify_certified_owner(repo,row,hit,foundation,'CP605',
        package_name,'.Calculation.Cursor.ActionMatrix','002')
    require(row['tracked_source_commit']==foundation and cert['matrix_data_ancestry']==inputs['matrix_data_ancestry'] and
        all(cert['matrix_data_ancestry'].values()), 'CP605 exact original actor and effects drift')
    sibling, = [entry for entry in stage['inputs'] if entry['module'].endswith('.Runtime.TimelineBasis')]
    signed, = [entry for entry in inputs['science'] if entry['module']==sibling['module']]
    strict = read(exact(sibling['receipt']))
    sibling_hit = select(sibling['module'])
    source = repo/sibling['main']
    require(sibling['final_attempt']==strict['attempt']=='005' and strict['exit_code']==0 and
        strict['source_unchanged'] and strict['old_compilations']==0 and strict['command']==sibling['strict_command'] and
        tracked_source_sha(repo,foundation,source)==sha(source)==sibling['source_sha256']==
            signed['source_sha256']==strict['source_sha256']==sha(strict['source_snapshot']) and
        sibling_hit.samefile(exact(sibling['object'])) and sibling_hit.samefile(exact(strict['object'])) and
        sha(sibling_hit)==signed['artifact_sha256'], 'CP605 exact incidence helper drift')
    prior_package = repo/'Verification/no-island'/package_name
    prior_paid = prior_package/'evidence/paid-parents.json'
    require(sha(prior_paid)==sha(exact(stage['paid_parent_bindings']))==inputs['frozen_inputs']['paid-parent-bindings.json'],
        'CP605 original actor ancestry bindings drift')
    prior_verifier = prior_package/'certify.py'
    require(sha(prior_verifier)==inputs['local_evidence_sha256']['certify.py']==
        tracked_source_sha(repo,foundation,prior_verifier),'CP605 static verifier identity drift')
    prior = {'__name__':'_cp605_frozen_provenance_'}
    exec(compile(prior_verifier.read_text(),str(prior_verifier),'exec'),prior)
    prior['verify_mathlib'] = prior['verify_batteries'] = verify_old_pin
    paid = read(prior_paid)['rows']
    require(len(paid)==3 and {entry['module'].rsplit('.',1)[-1] for entry in paid}==
        {'MatrixBorder','FirstCompletion','Basic'}, 'CP605 exact signed ancestor scope drift')
    for parent in paid:
        prior['verify_parent'](repo,parent,select,stage['foundation_commit'])


def pinned_locks():
    return {'current_lock_commit':LOCK_NEW_COMMIT,'current_lock_sha256':LOCK_NEW_SHA,
            'prior_signed_lock_sha256':LOCK_OLD_SHA,'source_foundation':CP605_COMMIT,
            'package_revisions':REVISIONS,'direct':PINS,'inherited':OLD_PINS}


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
        require(module.startswith('SaturationMonoid.') and module.endswith(('.FiniteGram.SparseMoment','.Calculation.Cursor.NativeMomentPulse')) and
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

    paid_path = package/'evidence/paid-parents.json'
    paid = read(paid_path)
    parents = paid['rows']
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(paid['schema']=='sparse-moment-source-paid-parents/v1' and
            len(parents)==4 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base'])=={row['module'] for row in parents}, 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['output'])
    require(output['schema']=='sparse-moment-source-output/v1' and
            Path(output['import_view'])==roots[0] and
            output['owned_old_recompiles']==0 and physical.is_relative_to('runtime/ and
            Path(stage['lean_root']).resolve()==physical/'source-root/main' and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','source-root','receipts')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' for row in frozen.values()),
            'second SSD output binding drift')
    for row in parents:
        verify_parent(args.repo,row,lambda module: selected(module,roots)[0],stage['foundation_commit'])
    require(inputs['pinned_locks']==pinned_locks(), 'source pin scope drift')
    require(read(exact(stage['compiler_companions']))['companions']==[], 'unexpected compiler runtime companions')
    return inputs,roots,science_actual


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['duplicates'] == 0 and
            stage['inherited'] == counts['inherited'] == report['inherited_generated_full_CI_matches'] and
            stage['fresh_replayed'] == counts['safe'] == report['fresh_safe_replayed_CIs'] and
            stage['fresh_replayed']+stage['inherited']==stage['raw'] and
            not stage['base_has_unverified_sources'] and not stage['compiler_runtime'] and
            report['fresh_raw_regions'] == 2 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    owners = {r['module']:r for r in actual}
    for owner in stage['modules']:
        selected_owner = owners.pop(owner['module'])
        require(sha(owner['selected_olean']) == selected_owner['artifact_sha256'] and
                owner['raw'] == selected_owner['raw_CIs'] and owner['imports'] == selected_owner['raw_imports'] and
                owner['compiler_extras'] == selected_owner['compiler_extras'] and
                owner['compiler_extra_names'] == selected_owner['compiler_extra_names'],
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
    binders = {row['name'].rsplit('.',1)[-1]:(row['input_binders'],row['result_arrows'])
        for row in report['public_mouths']}
    all_types = ['I','K','inst']
    field = ['K','inst']
    prefix = all_types+['clock','distinct','source','bound','within']
    recover_at = all_types+['clock','distinct','available','source','availableSource','bound','within']
    public = {
        'moments':(all_types+['clock','source','degree'],0),
        'measure':(all_types+['clock','source','bound'],1),
        'hankel':(['K','data','rank'],0),
        'order':(field+['bound','data'],0),
        'hankel_factor':(all_types+['clock','source','width'],0),
        'order_from_source':(prefix,0),
        'recurrence':(field+['bound','data'],0),
        'recurrence_vanishes':(prefix+['site','active'],0),
        'recoverSupport':(all_types+['bound','clock','available','data'],0),
        'recover_support':(recover_at,0),
        'recover':(all_types+['bound','clock','available','data'],0),
        'recover_prefix':(recover_at,0),
        'clock':(['depth','site'],0),
        'effectRows':(['depth','i'],1),
        'decode':(['depth','data'],0),
        'decoded_effect':(['depth','i'],0),
        'actual_increment':(['depth','i'],0),
        'held_decodes_zero':(['depth','i','after'],0),
        'terminalRows':(['depth'],1),
        'actual_terminal':(['depth'],0),
    }
    require(binders==public, 'measured Hankel system or original Goldbach actor binder drift')
    require(stage['kernel_calls']==stage['fresh_replayed']==counts['safe']==74, 'fresh CI coverage drift')
    ancestry = report['moment_data_ancestry']
    require(ancestry==inputs['moment_data_ancestry'] and all(ancestry.values()) and len(ancestry)==6,
            'moment selection or complete original actor data flow drift')
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
    save(output/'provenance.json',{'schema':'cp614-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':4,'gate_ancestor_bindings':9,'verification_overlay_objects':0,'pinned_locks':inputs['pinned_locks'],'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':4,'gate_ancestor_bindings':9,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp614-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP614_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp614-source-sparse-moment-goldbach','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp614-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
