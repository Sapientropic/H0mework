#!/usr/bin/env python3
"""Verify the CP805 original counted cell, finite Cayley entrance, and paid writeback."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

FLAGS = ['--trust=0', '-DElab.async=false', '-DwarningAsError=true', '-DmaxErrors=1',
         '-j1', '-M32000', '-DstderrAsMessages=false']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
STAGE_SHA = 'c739b5c1a8d39fd6c3fb49660834585aa58e057b8cd61c1e24555af3619d9291'
PRIOR_STAGE_SHA = 'dc448421beb037f63d25eb57fb8a1e919b5d7871cc5c30fe9a4b3fca3f9b5c01'
PRIOR_PUBLICATION = '50db745b0e75d082acd1f040d7e0aa02757d1ff2'
PRIOR_CERT_SHA = 'cf6c48fad0cde31bdcf0c0aff30a81e1ebff14b35ad08b27bde3a88e840bbc27'
POWER_MODULE = ('SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.'
                'Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.'
                'Source.Action.Finite.Source.PowerWave')
POWER_SOURCE_SHA = '6d04b5c4336e46bbe00fb03621059648a1d95728af4b7fafdd2bf73870d7ffeb'
POWER_OBJECT_SHA = '7d596771ff355ba69d557f15d3abbbe12d0bfaf54374d9075eba5c1087bc0647'
ATTEMPTS = [('Average','004'),('Cayley','004'),('Programme','005'),('Receipt','003')]
SCOPE = [(3,0,0,0),(30,14,0,115),(73,58,2,329),(44,38,0,427)]
CONTROLS = [
    ['+','original_drive_is_generated_by_the_cayley_action'],
    ['+','paid_count_is_the_retained_child_of_the_finite_entrance'],
    ['+','finite_error_is_paid_by_the_original_predecessor'],
    ['+','the_same_finite_entrance_has_exact_signed_Fourier'],
    ['+','limit_feeds_original_slots_and_independent_K'],
    ['+','actual_paid_relation_cochain_fibre_whole_and_next'],
    ['-','zero_iterations_keeps_successor_but_omits_nonzero_actual_entrance'],
]
PACKAGE_FILES = {'Audit.lean','Gate.lean','README.md','audit-summary.json','certificate.json',
                 'certify.py','independent-cost.json','inputs.json'}


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def write(path, data):
    with Path(path).open('x') as stream:
        json.dump(data,stream,indent=2)
        stream.write('\n')


def exact(record):
    path = Path(record['path'])
    require(path.stat().st_size==record['bytes'] and sha(path)==record['sha256'],f'evidence drift {path}')
    return path


def tracked(repo, revision, path):
    relative = Path(path).relative_to(repo)
    blob = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',revision+':'+str(relative)],cwd=repo)
    return hashlib.sha256(blob).hexdigest()


def first_hit(module, roots):
    package = module.split('.')[0]
    relative = Path(*module.split('.')).with_suffix('.olean')
    root = next(root for root in roots if (root/package).is_dir() or (root/(package+'.olean')).is_file())
    path = root/relative
    require(path.is_file(),f'missing selected object {module}')
    return path


def verify_paid(repo, stage, inputs, roots):
    parents = read(exact(stage['paid_parent_bindings']))
    require(Counter(row['kind'] for row in parents.values()) ==
            {'certified-prior-owner':33,'original-division-action':1,'installed-library':7,'paid-view-base':5},
            'frozen paid scope drift')
    old_stage_path = exact(stage['prior_stage'])
    old_stage = read(old_stage_path)
    require(stage['prior_stage']['sha256']==PRIOR_STAGE_SHA,'CP801 frozen stage drift')
    old_parents = read(exact(old_stage['paid_parent_bindings']))
    require(set(old_parents)<=set(parents) and all(
        parents[module]['object']['sha256']==row['object']['sha256'] and
        {k:v for k,v in parents[module].items() if k!='object'}=={k:v for k,v in row.items() if k!='object'}
        for module,row in old_parents.items()),'CP801 inherited view drift')
    prior = repo/'Verification/no-island/riemann-r-counted-exact-incidence'
    old_cert_path = prior/'certificate.json'
    old_inputs_path = prior/'inputs.json'
    old_cert = read(old_cert_path)
    old_inputs = read(old_inputs_path)
    require(old_cert['checkpoint']=='CP801' and old_cert['verdict']=='certified'
            and old_cert['stage_map']==stage['prior_stage'] and sha(old_inputs_path)==old_cert['inputs_sha256']
            and sha(old_cert_path)==PRIOR_CERT_SHA
            and tracked(repo,PRIOR_PUBLICATION,old_cert_path)==sha(old_cert_path)
            and tracked(repo,PRIOR_PUBLICATION,old_inputs_path)==sha(old_inputs_path),'CP801 publication binding drift')
    extra = inputs['additional_paid']
    require(len(extra)==7 and set(extra).isdisjoint(parents),'additional paid CI owner scope drift')
    power = extra[POWER_MODULE]
    require(power['kind']=='paid-closure-owner' and power['source']['sha256']==POWER_SOURCE_SHA
            and power['object']['sha256']==POWER_OBJECT_SHA,'exact source Cayley definition owner drift')
    require(set(extra)==set(old_inputs['additional_paid'])|{POWER_MODULE} and all(
        extra[module]['kind']==row['kind'] and extra[module]['source']==row['source']
        and extra[module]['object']['sha256']==row['object']['sha256']
        for module,row in old_inputs['additional_paid'].items()),
            'prior auxiliary evidence scope drift')
    for module,row in (parents|extra).items():
        require(first_hit(module,roots)==exact(row['object']),f'paid first hit drift {module}')
        kind = row['kind']
        if kind=='installed-library':
            continue
        source = exact(row['source'])
        require(tracked(repo,stage['foundation_commit'],source)==row['source']['sha256'],f'paid source Git drift {module}')
        if kind in ('paid-view-base','paid-closure-owner'):
            continue
        if kind=='prior-paid-source':
            authority = exact(row['authority'])
            inherited = old_inputs['additional_paid'][module]
            old, = [r for r in read(authority)['added_rows'] if r['module']==module]
            require(tracked(repo,stage['foundation_commit'],authority)==row['authority']['sha256']
                    and inherited['source']==row['source'] and inherited['authority']==row['authority']
                    and old['source_sha256']==row['source']['sha256'] and old['object_sha256']==row['object']['sha256'],
                    f'prior exact source authority drift {module}')
            continue
        certificate = exact(row['certificate'])
        cert = read(certificate)
        require(cert['verdict']=='certified' and set(cert['axioms'])<=AXIOMS and
                tracked(repo,stage['foundation_commit'],certificate)==row['certificate']['sha256'],
                f'certified parent drift {module}')
        if kind=='original-division-action':
            original = read(exact(row['stage_map']))
            owner, = [r for r in original['paid_inputs'] if r['module']==module]
            exact(row['evidence'])
            require(cert['checkpoint']=='CP796' and owner['old_direct'] and owner['authority']==row['evidence']
                    and owner['source_sha256']==row['source']['sha256'] and owner['object']['sha256']==row['object']['sha256'],
                    'original CP321 action provenance drift')
        else:
            require(kind=='certified-prior-owner',f'unrecognized paid source {kind}')
            signed_inputs = exact(row['inputs'])
            owner, = [r for r in read(signed_inputs)['science'] if r['module']==module]
            require(tracked(repo,stage['foundation_commit'],signed_inputs)==row['inputs']['sha256']
                    and owner['source_sha256']==row['source']['sha256'] and owner['artifact_sha256']==row['object']['sha256'],
                    f'certified owner bytes drift {module}')
    return parents|extra


def verify_cost(stage, inputs, package):
    construction = read(exact(stage['construction_cost']))
    rows = construction['attempts']
    require(construction['total_lean_calls']==len(rows)==17 and construction['failed_calls']==12 and
            construction['old_source_calls']==construction['old_source_successes']==0 and
            abs(construction['total_seconds']-sum(r['elapsed_seconds'] for r in rows))<1e-9,'construction cost drift')
    for row in rows:
        path = exact(row['receipt'])
        receipt = read(path)
        log = path.with_name(path.name.replace('.receipt.json','.log'))
        require(receipt['exit_code']==row['exit_code'] and receipt['elapsed_seconds']==row['elapsed_seconds']
                and receipt['old_compilations']==0 and receipt['lean_path_sha256']==stage['lean_path']['sha256']
                and receipt['source_sha256']==sha(receipt['source_snapshot']) and receipt['log_sha256']==sha(log),
                f'construction evidence drift {path.name}')
    raw = read(exact(stage['raw_inventory_receipt']))
    require(raw['exit_code']==0 and raw['command'][-4:]==[f'{a}-{b}' for a,b in ATTEMPTS],'raw inventory call drift')
    for sample in stage['diagnostics']:
        exact(sample)
    exact(stage['output_location'])
    path = package/'independent-cost.json'
    require(sha(path)==inputs['independent_cost_sha256'],'independent cost binding drift')
    cost = read(path)
    attempts = cost['attempts']
    require(cost['total_lean_calls']==len(attempts)
            and abs(cost['total_seconds']-sum(r['elapsed_seconds'] for r in attempts))<1e-9
            and cost['old_source_recompiles']==cost['old_ci_replays']==0,'independent cost drift')
    require(cost['successful_calls']==sum(r['exit_code']==0 for r in attempts)==2
            and cost['failed_natural_calls']==sum(r['exit_code']>0 for r in attempts)
            and cost['owner_stopped_calls']==cost['unknown_cost_calls']==0
            and all(r['natural_exit'] for r in attempts),'independent exit accounting drift')
    for row in attempts:
        receipt = read(exact(row['receipt']))
        require(receipt['elapsed_seconds']==row['elapsed_seconds'] and receipt['exit_code']==row['exit_code']
                and receipt['natural_exit']==(receipt['exit_code']>=0) and receipt['source_unchanged']
                and receipt['old_source_recompiles']==receipt['old_ci_replays']==0
                and receipt['lean_path']==stage['lean_path'] and set(FLAGS)-{'-DmaxErrors=1'}<=set(receipt['command']),
                f'independent invocation drift {receipt["label"]}')
        exact(receipt['snapshot'])
        exact(receipt['log'])
        if receipt['config'] is not None:
            require(exact(row['config_snapshot']).stat().st_size==receipt['config']['bytes']
                    and row['config_snapshot']['sha256']==receipt['config']['sha256'],
                    f'independent configuration snapshot drift {receipt["label"]}')
        else:
            require(row['config_snapshot'] is None,'unexpected Gate configuration')
    for field,file in (('strict_gate_receipt','Gate.lean'),('strict_audit_receipt','Audit.lean')):
        receipt = read(exact(inputs[field]))
        require(receipt['exit_code']==0 and receipt['natural_exit'] and set(FLAGS)-{'-DmaxErrors=1'}<=set(receipt['command'])
                and receipt['source']['sha256']==sha(package/file),
                f'accepted command/source drift {file}')
        if file=='Gate.lean':
            log = exact(receipt['log'])
            require(control_rows(log)==CONTROLS and
                    'CP805_GATE_PASS positive=6 negative=1' in log.read_text().splitlines(),
                    'accepted typed controls drift')
        else:
            require(receipt['config']==inputs['audit_config_receipt']
                    and read(exact(receipt['config']))==inputs['audit_config'],
                    'accepted replay configuration drift')


def verify_inputs(package,args):
    inputs = read(package/'inputs.json')
    for name,digest in inputs['code'].items():
        require(sha(package/name)==digest,f'checker source drift {name}')
    stage_path = exact(inputs['stage_map'])
    stage = read(stage_path)
    view = exact(stage['lean_path'])
    roots = [Path(root) for root in view.read_text().strip().split(os.pathsep)]
    require(inputs['stage_map']['sha256']==STAGE_SHA and stage['schema']=='cp805-frozen-stage/v1'
            and stage['frozen'] and not stage['refreshed_old_sources'] and view.samefile(args.base_lean_path_file)
            and roots[0].samefile(args.compiled_root) and roots[0]==Path(stage['compiled_root']),'frozen view drift')
    parents = verify_paid(args.repo,stage,inputs,roots)
    verify_cost(stage,inputs,package)
    raw = read(exact(stage['raw_ci_inventory']))
    config = inputs['audit_config']
    new,owners = stage['inputs'],config['modules']
    require(raw['regions_read']==len(raw['rows'])==len(new)==len(owners)==4
            and [(row['stage'],row['final_attempt']) for row in new]==ATTEMPTS,'raw owner scope drift')
    with gzip.open(exact(inputs['source_restore']),'rb') as stream:
        restore = json.load(stream)
    source_root = args.source_root or args.repo/'Lean'
    for row,inventory,owner,(raw_count,private,partial,extras) in zip(new,raw['rows'],owners,SCOPE,strict=True):
        module = row['module']
        relative = Path(*module.split('.')).with_suffix('.lean')
        source = source_root/relative
        selected = first_hit(module,roots)
        physical = exact(row['object'])
        receipt = read(exact(row['receipt']))
        require(row['main']==str(Path('Lean')/relative) and source.read_bytes()==Path(row['source']).read_bytes()
                ==restore[row['main']].encode() and sha(source)==row['source_sha256']==receipt['source_sha256']
                and receipt['source_unchanged'] and receipt['exit_code']==receipt['old_compilations']==0
                and receipt['command']==row['strict_command'] and set(FLAGS[:3])<=set(receipt['command'])
                and selected.samefile(physical) and selected.samefile(exact(receipt['object'])),
                f'selected source/strict output drift {module}')
        require(owner['name']==module and owner['selected']==str(selected) and Path(owner['physical']).samefile(physical)
                and inventory['raw']==row['raw']==owner['count']==raw_count
                and inventory['private']==row['private']==owner['privateCount']==private
                and inventory['unsafe']==0 and inventory['partial']==partial
                and [ci['name'] for ci in inventory['constants'] if ci['partial']]==owner['runtime']
                and set(owner['runtime'])==set(row['compiler_runtime'])
                and len(inventory['compiler_extra_names'])==extras
                and inventory['compiler_extra_names']==row['compiler_extra_names']==owner['extras']
                and inventory['imports']==row['imports']==owner['imports']
                and [ci['name'] for ci in inventory['constants']]==owner['names'],f'raw inventory drift {module}')
    runtime = stage['compiler_runtime']
    flat = {ci['name']:ci for inv in raw['rows'] for ci in inv['constants']}
    require(len(flat)==150 and set(runtime)=={name for name,ci in flat.items() if ci['partial']},
            'compiler companion partition drift')
    for name,row in runtime.items():
        require(flat[name]['private'] and not flat[name]['unsafe']
                and flat[row['parent']]['kind']=='definition' and not flat[row['parent']]['partial']
                and [n for n,ci in flat.items() if name in ci['used_constants']]==row['incoming']==[name],
                f'compiler companion leakage {name}')
    require(set(restore)=={row['main'] for row in new} and inputs['typed_controls']==CONTROLS
            and [line.split()[1] for line in (package/'Gate.lean').read_text().splitlines() if line.startswith('import ')]
            ==[new[-1]['module']],'restore or direct gate scope drift')
    require(config['paidSelected']==[[name,row['object']['path']] for name,row in parents.items()]
            and set(config['base'])=={module for row in new for module in row['imports'] if module!='Init'
                                      and module not in {row['module'] for row in new}},'paid base scope drift')
    return inputs,stage,roots


def validate_report(report,inputs,stage):
    config = inputs['audit_config']
    expected = inputs['counts']
    require(report['schema']=='cp805-raw-first-private-body-audit/v1' and report['accepted']
            and report['raw_CIs']==150 and report['logical_CIs']==148 and report['compiler_extras']==871
            and report['kernel_calls']==expected['kernel_calls']
            and len(report['inherited_full_CIs'])==expected['inherited']
            and report['axiom_closure']==expected['axiom_closure'] and set(report['axioms'])==AXIOMS
            and report['old_source_replays']==0 and report['subject_free_base_imports']==1
            and report['candidate_environment_imports']==0 and report['source_target_reads']==[],
            'kernel scope, closure, or axiom drift')
    require(report['body_edges']==config['bodyEdges'] and report['type_edges']==config['typeEdges']
            and [r['name'] for r in report['mouths']]==[row[0] for row in config['mouths']]
            and len(report['paid_CIs'])==len(config['paidSource'])==expected['paid_source_CIs']
            and len(report['paid_selected'])==53 and len(report['public_mouth_axioms'])==expected['public_mouths']
            and all(set(row['axioms'])<=AXIOMS for row in report['public_mouth_axioms'])
            and report['finite_data_exclusions']==config['dataExclusions']
            and report['finite_data_paid_definitions']==expected['finite_data_paid_definitions'],
            'producer or original consumer DAG drift')
    runtime = {row['name']:row for row in report['compiler_runtime_CIs']}
    require(set(runtime)==set(stage['compiler_runtime']) and len(runtime)==2,
            'audited compiler companion scope drift')
    for name,row in runtime.items():
        expected_runtime = stage['compiler_runtime'][name]
        require(row['parent']==expected_runtime['parent'] and row['incoming']==[name]
                and row['partial'] and not row['unsafe'] and row['kind']=='definition',
                f'audited compiler companion drift {name}')
    require(len(report['declarations'])==148
            and sum(r['name'].startswith('_private.') for r in report['declarations'])==108,
            'private logical CI drift')
    for actual,row in zip(report['modules'],stage['inputs'],strict=True):
        companions = len(row['compiler_runtime'])
        require(actual['module']==row['module'] and actual['raw']==row['raw']
                and actual['logical']==row['raw']-companions and actual['raw_private']==row['private']
                and actual['private']==row['private']-companions
                and set(actual['compiler_runtime_names'])==set(row['compiler_runtime'])
                and actual['imports']==row['imports'] and actual['compiler_extra_names']==row['compiler_extra_names']
                and sha(actual['selected'])==row['object']['sha256'],f'audited owner drift {row["module"]}')


def verify_package(package):
    manifest = read(package/'manifest.json')
    members = {row['path']:row for row in manifest['members']}
    require(manifest['checkpoint']=='CP805' and set(members)==PACKAGE_FILES,
            'published package scope drift')
    for name,row in members.items():
        path = package/name
        require(path.stat().st_size==row['bytes'] and sha(path)==row['sha256'],
                f'published package member drift {name}')
    cert = read(package/'certificate.json')
    require(cert['checkpoint']=='CP805' and cert['verdict']=='certified'
            and cert['inputs_sha256']==members['inputs.json']['sha256']
            and cert['audit_summary_sha256']==members['audit-summary.json']['sha256']
            and cert['independent_cost_sha256']==members['independent-cost.json']['sha256'],
            'certificate member drift')


def control_rows(log):
    prefix = 'CP805_CONTROL '
    return [line[len(prefix):].split(' ',1) for line in Path(log).read_text().splitlines() if line.startswith(prefix)]


def run(args,package,config,roots):
    require(args.output is not None,'supply a fresh --output directory for replay')
    args.output.mkdir(parents=True,exist_ok=True)
    output = args.output.resolve()
    config = {**config,'output':str(output/'audit-summary.json'),'progress':str(output/'audit-progress.jsonl'),
              'current':str(output/'audit-current.json')}
    config_path = output/'audit-config.json'
    write(config_path,config)
    lean = args.lean or Path(subprocess.check_output(['elan','which','lean'],cwd=args.repo/'Lean',text=True).strip())
    env = {**os.environ,'LEAN_PATH':os.pathsep.join(map(str,roots)),
           'LEAN_SYSROOT':str(lean.resolve().parent.parent),'LEAN_NUM_THREADS':'1'}
    for label,file in (('001-gate','Gate.lean'),('002-audit','Audit.lean')):
        source,log = package/file,output/(label+'.log')
        command = [str(lean),*FLAGS]
        command += ['--run',str(source),str(config_path)] if file=='Audit.lean' else [str(source)]
        start = time.monotonic()
        with log.open('xb') as stream:
            status = subprocess.call(command,cwd=output,env=env,stdout=stream,stderr=subprocess.STDOUT)
        write(output/(label+'.receipt.json'),dict(command=command,exit_code=status,natural_exit=status>=0,
              seconds=time.monotonic()-start,source_sha256=sha(source),log_sha256=sha(log),old_source_recompiles=0,old_ci_replays=0))
        if status:
            print(log.read_text(errors='replace')[-7000:])
            raise SystemExit(status if status>=0 else 128-status)
        if file=='Gate.lean':
            require(control_rows(log)==CONTROLS,'typed controls drift')
    return read(output/'audit-summary.json')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('repo','compiled-root','base-lean-path-file'):
        parser.add_argument('--'+option,type=Path,required=True)
    for option in ('output','source-root','lean'):
        parser.add_argument('--'+option,type=Path)
    parser.add_argument('--verify-inputs-only',action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    verify_package(package)
    inputs,stage,roots = verify_inputs(package,args)
    report = read(exact(inputs['recorded_raw_audit'])) if args.verify_inputs_only else run(args,package,inputs['audit_config'],roots)
    validate_report(report,inputs,stage)
    print(json.dumps(dict(verdict='exact-inputs-and-recorded-audit-verified' if args.verify_inputs_only else 'certified',
          raw_CIs=150,logical_CIs=148,private_logical_CIs=108,compiler_runtime_CIs=2,compiler_extras=871,
          kernel_calls=report['kernel_calls'],inherited_full_CIs=len(report['inherited_full_CIs']),
          independent_lean_calls=0 if args.verify_inputs_only else 2,old_source_recompiles=0,old_ci_replays=0)))


if __name__=='__main__':
    main()
