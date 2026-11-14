#!/usr/bin/env python3
"""Verify the retained Schur inverse update and its original R readback."""
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


def verify_cp601(repo,row,hit,foundation):
    module = row['module']
    require(row['binding_kind']=='exact-certified-source-reuse' and module.endswith('.ResidualProbe.RetainedRecord'),
        'unexpected CP601 provider '+module)
    manifest_path,cert_path,promotion_path,stage_path,receipt_path = map(exact,row['bindings'])
    manifest,cert,promotion,stage,receipt = map(read,(manifest_path,cert_path,promotion_path,stage_path,receipt_path))
    package = repo/'Verification/no-island/riemann-r-retained-gram-record'
    inputs_path = package/'inputs.json'
    inputs = read(inputs_path)
    revision = row['tracked_source_commit']
    require(revision==foundation and manifest_path==package/'manifest.json' and cert_path==package/'certificate.json' and
        manifest['checkpoint']==cert['checkpoint']=='CP601' and cert['verdict']=='certified' and
        set(cert['axioms'])=={'propext','Classical.choice','Quot.sound'} and
        cert['prior_schedule_ancestry']==inputs['prior_schedule_ancestry'] and
        cert['retained_data_ancestry']==inputs['retained_data_ancestry'] and all(inputs['retained_data_ancestry'].values()), 'CP601 certificate identity drift')
    for path in (manifest_path,cert_path,inputs_path,repo/row['main']):
        require(tracked_source_sha(repo,revision,path)==sha(path), 'CP601 tracked bytes drift '+str(path))
    for path in (cert_path,inputs_path):
        entry, = [r for r in manifest['members'] if r['path']==path.name]
        require(entry['sha256']==sha(path) and entry['bytes']==path.stat().st_size,
            'CP601 manifest binding drift '+str(path))
    require(cert['inputs']['sha256']==sha(inputs_path) and cert['inputs']['bytes']==inputs_path.stat().st_size and
        cert['main_promotion']['sha256']==sha(promotion_path) and
        cert['main_promotion']['bytes']==promotion_path.stat().st_size and
        inputs['frozen_inputs']['stage-map.json']==sha(stage_path)==promotion['stage_map_sha256'] and
        stage['frozen'] and promotion['exact'] and promotion['old_compilations']==0, 'CP601 promotion / stage drift')
    final, = [r for r in stage['inputs'] if r['module']==module]
    promoted, = [r for r in promotion['inputs'] if r['module']==module]
    authority = exact(row['authority_object'])
    require(final['main']==promoted['main']==row['main'] and
        final['source_sha256']==promoted['source_sha256']==row['source_sha256']==sha(repo/row['main']) and
        Path(final['source'])==Path(receipt['source']) and
        sha(receipt['source_snapshot'])==receipt['source_sha256']==row['source_sha256'] and
        exact(final['receipt'])==receipt_path and promoted['receipt_sha256']==sha(receipt_path) and
        final['final_attempt']==receipt['attempt']=='010' and
        receipt['command']==final['strict_command'] and receipt['exit_code']==0 and
        receipt['source_unchanged'] and receipt['old_compilations']==0 and
        {'--trust=0','-DElab.async=false','-DwarningAsError=true'}<=set(receipt['command']),
        'CP601 strict/source binding drift '+module)
    require(all(hit.samefile(path) for path in
                (authority,row['object'],row['provider'],exact(final['object']),exact(receipt['object']))) and
        sha(hit)==row['object_sha256']==promoted['object_sha256']==final['object']['sha256'],
        'CP601 selected object drift '+module)






def verify_cp476(repo,row,hit,foundation):
    module = row['module']
    source = repo/row['main']
    flags = {'--trust=0','-DElab.async=false','-DwarningAsError=true'}
    require(row['binding_kind']=='exact-cp476-certified-source-reuse' and
        module=='SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection',
        'unexpected CP476 provider '+module)
    set_path,proof_path,tx_path,cert_path,capsule_path,pub_path,snapshot,receipt_path = map(exact,row['bindings'])
    source_set,proof,tx,cert,capsule,pub,receipt = map(read,
        (set_path,proof_path,tx_path,cert_path,capsule_path,pub_path,receipt_path))
    require(source_set['checkpoint']==proof['checkpoint']==tx['checkpoint']==pub['checkpoint']=='CP476' and
        source_set['machine_finalized'] and source_set['current_finalized'] and
        tx['publisher_exit']==0 and pub['commit']==row['tracked_source_commit']=='bc64eb1c29097689ba7ea2ea2d417b4f9ff6bd21' and
        exact(tx['publication_result'])==pub_path and exact(proof['source_set'])==set_path and
        exact(source_set['independent_certificate'])==exact(proof['certificate'])==cert_path and
        exact(source_set['frozen_capsule'])==exact(cert['frozen_capsule'])==exact(proof['frozen_capsule'])==capsule_path and
        cert['verdict']=='PASS' and set(cert['standard_axioms'])=={'propext','Classical.choice','Quot.sound'} and
        cert['old_CI_or_getter_replays']==0 and cert['heavy_released'] and module in capsule['modules'],
        'CP476 frozen source set or publication chain drift')
    old, = [q for q in source_set['owned_sources'] if q['module']==module]
    promoted, = [q for q in tx['copied_sources'] if q['repoPath']==row['main']]
    authority = exact(row['authority_object'])
    require(old['repoPath']==row['main'] and source.samefile(old['destination']) and exact(old['frozen_source'])==snapshot and
        sha(source)==sha(snapshot)==old['new_sha256']==old['source']['sha256']==row['source_sha256']==promoted['sha256'] and
        source.samefile(promoted['path']) and promoted['bytes']==source.stat().st_size and
        all(tracked_source_sha(repo,rev,source)==row['source_sha256'] for rev in (foundation,pub['commit'])),
        'CP476 exact tracked Projection source drift')
    old_blob = subprocess.check_output(['git','--no-optional-locks','rev-parse',pub['commit']+':'+row['main']],
                                       cwd=repo,text=True).strip()
    require(pub['owned_entries'][row['main']]==['100644',old_blob], 'CP476 owned Git blob binding drift')
    require(exact(old['receipt'])==receipt_path and receipt['module']==module and receipt['strict_green'] and
        receipt['exit_code']==receipt['parent_recompile']==receipt['parent_copies']==receipt['Scope_runs']==0 and
        flags<=set(receipt['command']) and receipt['source']['sha256']==row['source_sha256'] and
        receipt['object']==old['object'] and exact(old['object']).samefile(authority) and
        all(hit.samefile(path) for path in (authority,row['object'],row['provider'])) and
        sha(hit)==row['object_sha256']==old['object']['sha256']==
            'f1f756afae69be1988a8521662b3781f316a540c844f50715af8ad6a2f4b4af9',
        'CP476 strict Projection body or receipt drift')
    guards = {Path(q['path']):q['sha256'] for q in proof['guards']}
    require(all(guards[path]==sha(path) for path in (snapshot,authority,receipt_path)),
        'CP476 exact Projection publication guards drift')


def verify_mathlib(repo,row,hit,foundation):
    module = row['module']
    source = Path(row['main'])
    require(row['binding_kind']=='pinned-mathlib' and module=='Mathlib.LinearAlgebra.Matrix.SchurComplement',
        'unexpected pinned Mathlib provider '+module)
    lake, = map(exact,row['bindings'])
    mathlib, = [r for r in read(lake)['packages'] if r['name']=='mathlib']
    checkout = repo/'Lean/.lake/packages/mathlib'
    relative = Path(*module.split('.')).with_suffix('.lean')
    revision = row['package_revision']
    head = subprocess.check_output(['git','--no-optional-locks','rev-parse','HEAD'],cwd=checkout,text=True).strip()
    require(lake.samefile(repo/'Lean/lake-manifest.json') and tracked_source_sha(repo,foundation,lake)==sha(lake) and
        head==mathlib['rev']==revision=='db584cd6d46c92f209a44c0f1c829460d327499d' and
        source.samefile(checkout/relative) and tracked_source_sha(checkout,revision,source)==sha(source)==row['source_sha256'] and
        all(hit.samefile(p) for p in (row['object'],row['provider'],checkout/'.lake/build/lib/lean'/relative.with_suffix('.olean'))) and
        sha(hit)==row['object_sha256'], 'pinned SchurComplement source or OLean drift')


def verify_parent(repo,row,hit,foundation):
    check = {'exact-certified-source-reuse':verify_cp601,
             'exact-cp476-certified-source-reuse':verify_cp476,'pinned-mathlib':verify_mathlib}[row['binding_kind']]
    check(repo,row,hit,foundation)


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


def verify_original_whole(args, roots, lineage):
    cert_path = exact(lineage['certificate'])
    signed = read(cert_path)
    prior_path = cert_path.with_name('inputs.json')
    prior = read(prior_path)
    paid_path = exact(lineage['paid_binding'])
    require(signed['checkpoint']=='CP557' and signed['verdict']=='certified' and set(signed['axioms'])==AXIOMS and
            signed['inputs']['sha256']==sha(prior_path) and
            prior['frozen_inputs']['paid-parent-bindings.json']==sha(paid_path) and
            prior['local_evidence_sha256']['evidence/paid-parents.json']==sha(paid_path),
            'original same-root whole provenance drift')
    whole, = [r for r in read(paid_path)['rows'] if r['module']==lineage['module']]
    hit,_ = selected(whole['module'],roots)
    require(whole['module'].endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction') and
            hit.samefile(whole['object']) and hit.samefile(whole['provider']) and
            sha(hit)==whole['object_sha256'] and sha(args.repo/whole['main'])==whole['source_sha256'],
            'original same-root whole/next selected body drift')
    root_cert, = [read(exact(attachment)) for attachment in whole['bindings']]
    require(root_cert['checkpoint']=='CP541' and root_cert['verdict']=='certified' and
            set(root_cert['axioms'])==AXIOMS, 'original Division root certificate drift')


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
        require(module.startswith('SaturationMonoid.') and module.endswith(('.FiniteGram.MatrixBorder','.ResidualProbe.RetainedMatrix')) and
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
    require(paid['schema']=='r-retained-schur-inverse-paid-parents/v1' and
            len(parents)==3 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base'])=={row['module'] for row in parents}, 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical_root'])
    require(Path(output['logical_stage'])==base and physical.is_relative_to('runtime/ and
            Path(output['objects'])==physical/'objects' and Path(output['receipts'])==physical/'receipts' and
            Path(output['source_root'])==physical/'source-root/main' and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','source-root','receipts')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' for row in frozen.values()),
            'second SSD output binding drift')
    for row in parents:
        hit,_ = selected(row['module'],roots)
        verify_parent(args.repo,row,hit,stage['foundation_commit'])
    certified = next(row for row in parents if row['binding_kind']=='exact-certified-source-reuse')
    inherited_gate = read(Path(certified['bindings'][1]['path']).with_name('inputs.json'))
    require(inherited_gate['gate_signed_science']==inputs['gate_signed_science'] and
            inherited_gate['whole_lineage']==inputs['whole_lineage'] and
            inherited_gate['retained_data_ancestry']==inputs['prior_retained_data_ancestry'], 'already paid Gate lineage drift')
    for ancestor in inputs['gate_signed_science']:
        verify_signed_science(args,roots,exact(ancestor['stage_map']),exact(ancestor['certificate']),
                              ancestor['checkpoint'],ancestor['module'])
    verify_original_whole(args,roots,inputs['whole_lineage'])
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
    frame = ['observation','nontrivial','half','depth','start','n']
    border = ['old','right','bottom','corner']
    public = {
        'border':border,
        'border_old_old':border+['i','j'],
        'border_old_new':border+['i'],
        'border_new_old':border+['j'],
        'border_new_new':border,
        'pivot':border,
        'border_det':border,
        'borderInverse':border+['unitPivot'],
        'columns':['A','j'],
        'coefficients_from_inverse':['A','input'],
        'observed':frame+['current'],
        'observed_entry_actual':frame+['current','row','actor'],
        'selectedRow':frame+['event','actor'],
        'observed_next':frame+['current'],
        'generated_pivot':frame+['current'],
        'MatrixState':frame,
        'extendMatrix':frame+['previous'],
        'runMatrix':frame,
        'run_matrix_source':frame,
        'determinant_update':frame+['previous'],
        'inverse_recovers':frame+['current','input'],
        'matrix_observes_records':frame+['current','a','b'],
        'extend_matrix_source':frame+['previous'],
        'inverse_reads_emitted':frame+['previous','a','b'],
    }
    generic = set(list(public)[:10])
    for name in generic | {'generated_pivot'}:
        named = [b for b in binders[name] if not b.startswith(('inst','_inst'))]
        binders[name] = named[-len(public[name]):] if name in generic else named
    require(binders==public, 'retained matrix or original consumer input drift')
    generated = stage['inductive_generated_full_CIs']
    require(generated==inputs['inductive_generated_full_CIs'] and len(generated)==counts['inductive_generated']==2 and
            {tuple(name.split('.')[-2:]) for name in generated}=={('MatrixState','mk'),('MatrixState','rec')} and
            stage['kernel_calls']+len(generated)==stage['fresh_replayed'], 'matrix state CI equality scope drift')
    ancestry = report['matrix_data_ancestry']
    require(ancestry==inputs['matrix_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'retained source, previous inverse or actual determinant data flow drift')
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
    save(output/'provenance.json',{'schema':'cp602-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':3,'gate_ancestor_bindings':2,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':3,'gate_ancestor_bindings':2,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp602-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP602_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp602-retained-schur-inverse','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp602-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
