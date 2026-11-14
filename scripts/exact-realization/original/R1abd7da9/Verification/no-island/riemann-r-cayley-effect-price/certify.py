#!/usr/bin/env python3
"""Verify the bounded Cayley-series inverse of the actual R effect and its complete price stream."""
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


def verify_parent(repo,row,select,foundation):
    module = row['module']
    hit = select(module)
    if row['binding_kind']=='pinned-mathlib':
        objects = {
            'Mathlib.Analysis.Complex.Basic':'1426b1a1a073fbdbf73c37f82a82f8cce3773b3a12a70389049e1f8aba412998',
            'Mathlib.Analysis.SpecificLimits.Normed':'ddeafa6978d30e920710f39a336030c98c0f2af390c0f05ce7b961a612d28fc0',
            'Mathlib.Tactic.Ring':'592377cbe645eff5792e1f62acbe0942fb9426841af93b4809cf468f3d79a99c',
        }
        require(module in objects and
            row['lock_commit']==foundation and row['lock_path']=='Lean/lake-manifest.json',
            'unexpected pinned Cayley series authority')
        lock = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
            foundation+':'+row['lock_path']],cwd=repo)
        require(hashlib.sha256(lock).hexdigest()==row['lock_sha256']==
            '29594f47ca4e85b19cf894013f40af6bee9a1e0e0ef51a1c846df7ca3d7379ea','frozen Mathlib lock drift')
        frozen, = [p for p in json.loads(lock)['packages'] if p['name']=='mathlib']
        live, = [p for p in read(repo/row['lock_path'])['packages'] if p['name']=='mathlib']
        checkout = repo/'Lean/.lake/packages/mathlib'
        head = subprocess.check_output(['git','--no-optional-locks','rev-parse','HEAD'],cwd=checkout,text=True).strip()
        source, object_authority = map(exact,row['bindings'])
        relative = Path(*module.split('.')).with_suffix('.lean')
        require(frozen==live and head==frozen['rev']==row['package_revision']==
            'db584cd6d46c92f209a44c0f1c829460d327499d' and
            source.samefile(checkout/relative) and source.samefile(row['main']) and
            tracked_source_sha(checkout,head,source)==sha(source)==row['source_sha256'] and
            object_authority.samefile(checkout/'.lake/build/lib/lean'/relative.with_suffix('.olean')) and
            all(hit.samefile(path) for path in (row['object'],row['provider'],object_authority)) and
            sha(hit)==row['object_sha256']==objects[module],
            'pinned Cayley series source or object drift')
        return
    if module.endswith('.SecondStockCayleyGrowth'):
        from types import SimpleNamespace

        package_name = 'riemann-r-cofinal-second-stock-recovery'
        stage,inputs,_ = verify_certified_owner(repo,row,hit,foundation,'CP584',
            package_name,'.SecondStockCayleyGrowth','003')
        signed_package = repo/'Verification/no-island'/package_name
        prior_paid = signed_package/'evidence/paid-parents.json'
        require(sha(prior_paid)==sha(exact(stage['paid_parent_bindings']))==
            inputs['frozen_inputs']['paid-parent-bindings.json'],'CP584 exact lifted-stock ancestry drift')
        verifier = signed_package/'certify.py'
        require(sha(verifier)==inputs['local_evidence_sha256']['certify.py']==
            tracked_source_sha(repo,row['tracked_source_commit'],verifier),'CP584 verifier identity drift')
        scope = {'__name__':'_cp584_frozen_lifted_stock_provenance_'}
        exec(compile(verifier.read_text(),str(verifier),'exec'),scope)
        owner, = [entry for entry in stage['inputs'] if entry['module']==module]
        needed = set(owner['imports'])-{'Init'}
        paid = [entry for entry in read(prior_paid)['rows'] if entry['module'] in needed]
        require(len(paid)==2 and {entry['module'] for entry in paid}==needed,'CP584 lifted-stock dependency drift')
        for ancestor in paid:
            chosen = select(ancestor['module'])
            root = chosen.parents[len(ancestor['module'].split('.'))-1]
            scope['verify_parent'](SimpleNamespace(repo=repo),[root],ancestor)
        return
    package_name = 'riemann-r-dense-price-stream'
    stage,inputs,cert = verify_certified_owner(repo,row,select(module),foundation,'CP617',
        package_name,'.ResidualProbe.DivisionPriceStream','001')
    require(row['tracked_source_commit']==foundation and
        cert['stream_data_ancestry']==inputs['stream_data_ancestry'] and
        all(cert['stream_data_ancestry'].values()), 'CP617 exact stream source provenance drift')
    prior_package = repo/'Verification/no-island'/package_name
    prior_paid = prior_package/'evidence/paid-parents.json'
    require(sha(prior_paid)==sha(exact(stage['paid_parent_bindings']))==inputs['frozen_inputs']['paid-parent-bindings.json'],
        'CP617 exact admitted stream ancestry drift')
    verifier = prior_package/'certify.py'
    require(sha(verifier)==inputs['local_evidence_sha256']['certify.py']==
        tracked_source_sha(repo,foundation,verifier),'CP617 verifier identity drift')
    scope = {'__name__':'_cp617_frozen_provenance_'}
    exec(compile(verifier.read_text(),str(verifier),'exec'),scope)
    nested, = [entry for entry in stage['inputs'] if entry['module'].endswith('.FiniteGram.PrefixImage')]
    chosen, = [entry for entry in stage['inputs'] if entry['module']==module]
    nested_source = repo/nested['main']
    nested_receipt = read(exact(nested['receipt']))
    require(nested['module'] in chosen['imports'] and select(nested['module']).samefile(exact(nested['object'])) and
        sha(nested_source)==tracked_source_sha(repo,foundation,nested_source)==nested['source_sha256'] and
        nested_receipt['exit_code']==0 and nested_receipt['source_unchanged'] and
        nested_receipt['source_sha256']==nested['source_sha256'] and
        exact(nested_receipt['object']).samefile(nested['object']['path']),
        'CP617 selected transitive PrefixImage drift')
    paid = read(prior_paid)['rows']
    require(len(paid)==2 and {entry['module'] for entry in paid} ==
        set(nested['imports']+chosen['imports'])-{'Init',nested['module']},'CP617 source ancestry scope drift')
    for ancestor in paid:
        scope['verify_parent'](repo,ancestor,select,stage['foundation_commit'])



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
        require(module.startswith('SaturationMonoid.') and module.endswith(('.Operator.CayleyEffectInverse','.ResidualProbe.DivisionEffectPrice')) and
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
    require(paid['schema']=='r-cayley-effect-price-paid-parents/v1' and
            len(parents)==5 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base'])=={row['module'] for row in parents}, 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['large_output'])
    require(Path(output['control'])==base and output['large_paths']==['objects','receipts','source-root'] and
            physical.is_relative_to('runtime/ and
            Path(stage['lean_root']).resolve()==physical/'source-root/main' and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in output['large_paths']) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' for row in frozen.values()),
            'second SSD output binding drift')
    for row in parents:
        verify_parent(args.repo,row,lambda module: selected(module,roots)[0],stage['foundation_commit'])
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
    binders = {'.'.join(row['name'].split('.')[-2:]):(row['input_binders'],row['result_arrows'])
        for row in report['public_mouths']}
    algebra = ['A','inst','inst']
    frame = ['observation','nontrivial','half','depth']
    public = {
        'CayleyEffectInverse.cayley': ([*algebra,'action','d'],0),
        'CayleyEffectInverse.inverse': ([*algebra,'action','d'],0),
        'CayleyEffectInverse.inverseBudget': (['d','budget'],0),
        'CayleyEffectInverse.inverse_effect': ([*algebra,'inst','action','d','budget','positive','growth'],0),
        'CayleyEffectInverse.inverse_norm': ([*algebra,'inst','action','d','budget','positive','growth'],0),
        'DivisionEffectPrice.effectInverse': (['observation','half'],0),
        'DivisionEffectPrice.inverse_equations': (['observation','half'],0),
        'DivisionEffectPrice.inverse_bound': (['observation','half'],0),
        **{f'DivisionEffectPrice.{name}':([*frame,'data'],0)
           for name in ('effect','effect_prices','recover','recover_effect','effect_recover')},
    }
    require(binders==public, 'Cayley-series or original effect binder drift')
    require(stage['kernel_calls']==stage['fresh_replayed']==counts['safe']==74, 'fresh CI coverage drift')
    ancestry = report['effect_inverse_data_ancestry']
    require(ancestry==inputs['effect_inverse_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'Cayley damping or original effect price data flow drift')
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
    save(output/'provenance.json',{'schema':'cp621-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':5,'gate_ancestor_bindings':29,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':5,'gate_ancestor_bindings':29,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp621-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP621_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp621-riemann-r-cayley-effect-price','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp621-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
