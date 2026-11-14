#!/usr/bin/env python3
"""Verify CP809 finite Wide graph recovery from the actual price difference and its native write."""
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
STAGE_SHA = 'a4ae94595620885b0e7ceeaef4bc189f5c8c650cab9758bb935b9691973989ab'
PRIOR_STAGE_SHA = '430fb30c3775333f6adbac04ed2a2a604a775ea1e2defd24cb362a0fae276e22'
PRIOR_PUBLICATIONS = {
    'riemann-r-counted-residual-inverse': ('CP808','ac9f88e1bf5dd1b7cd266fbc146196996100a55e',
        '22813be523c5c3dd8ee92eb8127bd473c527165ab450cf986d0fa492b9bed04a'),
    'riemann-r-cayley-effect-price': ('CP621','1abd7da932b7bb8c01560b105b55b11af347e5c7',
        'e7463e45bde221b2f045b35ad7a1e80f13f94898a85c5004a03fbad26b10160f'),
    'riemann-r-dense-price-stream': ('CP617','84e04d72a6c8e7a0f76164369cc3c46db942f3f4',
        '6778a11a5f63ea770c0af1027dd9999a7abb5c4087876d22e2fe301a41ade75c'),
    'riemann-r-price-stream-finite-write': ('CP618','f7e6a8f3c824092282f140b4c269d1a8d4d18274',
        'd7b6e9e3bd477e5e97dde437ad4c348ef3e94fe3dfce8e5808ac7b48027000a0'),
    'riemann-r-dense-division-price': ('CP615','2bdf137d2de645037a2696058f8d61efa0a5e784',
        'a5ba8a0aa03273a76719b5384162625a6f5aa576521f9ac27d9af21b60782881'),
    'riemann-r-finite-log-graph-recovery': ('CP568','31d6f5b3c3b673ea0cafa46aaaf369526591a242',
        'dffa981bc8c8d5bb6ee09aff06aee3ff73475b67f85c1e95b3b812408f0a43d8'),
    'riemann-r-physical-second-graph-inverse': ('CP575','c4ae9f7972c1e320831d1de6e62715325dd5ee82',
        '67081e18703d90d843f284720220cf62924114571175f84ca1613bafe8f85a68'),
    'riemann-r-single-slot-physical-price-inverse': ('CP577','62eba5a2ba540dbdd161229425ecda62a2508011',
        'e9240c2e1bb82c88ee18e2bd66a3206ce32d52110422d5575074d883ebef31f2'),
    'riemann-r-cofinal-second-stock-recovery': ('CP584','ec12840aa55ab6eec98e15d35a2558c1972eeea7',
        'a81804269a384496456cd1ce0235dfb3e580610769408139fd68acbfcd8f8602'),
}
ATTEMPTS = [('Growth','010'),('Gram','001'),('Source','010'),('Native','003'),('Consumer','008')]
SCOPE = [(10,2,0,63),(8,0,0,0),(66,36,0,392),(104,95,1,379),(50,36,0,401)]
CONTROLS = [
    ['+','actual_birth_bank_order_and_paid_price_difference'],
    ['+','paid_graph_has_separate_observation_and_action_error'],
    ['+','source_effect_recovers_the_nonzero_original_graph'],
    ['+','actual_write_executes_native_R_and_full_relation'],
    ['+','diagonal_recovers_closed_graph_and_independent_next_K'],
    ['+','paid_terminal_keeps_its_whole_next_and_original_macro'],
    ['-','zero_inverse_round_erases_both_graphs_and_misses_actual_stock'],
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
            {'certified-prior-owner':52,'original-division-action':1,'installed-library':9,'paid-view-base':10},
            'frozen paid scope drift')
    old_stage_path = exact(stage['prior_stage'])
    old_stage = read(old_stage_path)
    require(stage['prior_stage']['sha256']==PRIOR_STAGE_SHA,'CP808 frozen stage drift')
    old_parents = read(exact(old_stage['paid_parent_bindings']))
    require(set(old_parents)<=set(parents) and all(
        parents[module]['object']['sha256']==row['object']['sha256'] and
        {k:v for k,v in parents[module].items() if k!='object'}=={k:v for k,v in row.items() if k!='object'}
        for module,row in old_parents.items()),'CP808 inherited view drift')
    signed_publications = {}
    require(set(inputs['prior_publications'])==set(PRIOR_PUBLICATIONS),'direct publication scope drift')
    for package,(checkpoint,commit,expected_cert) in PRIOR_PUBLICATIONS.items():
        refs = inputs['prior_publications'][package]
        folder = repo/'Verification/no-island'/package
        certificate = exact(refs['certificate'])
        signed_inputs = exact(refs['inputs'])
        cert = read(certificate)
        inputs_digest = cert.get('inputs_sha256') or cert['inputs']['sha256']
        require(certificate==folder/'certificate.json' and signed_inputs==folder/'inputs.json'
                and refs['certificate']['sha256']==expected_cert
                and cert['checkpoint']==checkpoint and cert['verdict']=='certified'
                and inputs_digest==refs['inputs']['sha256'] and set(cert['axioms'])<=AXIOMS
                and tracked(repo,commit,certificate)==expected_cert
                and tracked(repo,commit,signed_inputs)==refs['inputs']['sha256'],
                f'{checkpoint} exact publication drift')
        if checkpoint=='CP808':
            require(cert['stage_map']==stage['prior_stage'],'CP808 signed stage drift')
        signed_publications[package] = read(signed_inputs)
    for package,suffix in (('riemann-r-dense-price-stream','.FiniteGram.PrefixImage'),
                           ('riemann-r-price-stream-finite-write','.PrefixImage.PrefixEnergy')):
        module, = [name for name in parents if name.endswith(suffix)]
        paid_row, = [r for r in signed_publications[package]['science'] if r['module']==module]
        require(paid_row['source_sha256']==parents[module]['source']['sha256']
                and paid_row['artifact_sha256']==parents[module]['object']['sha256'],
                f'original finite Gram provenance drift {module}')
    extras = inputs['additional_paid']
    require(len(extras)==16 and set(extras).isdisjoint(parents)
            and Counter(row['kind'] for row in extras.values())==
            {'paid-closure-owner':8,'certified-prior-owner':8},'supporting owner scope drift')
    require(Counter(row.get('inherited_from') for row in extras.values())=={'CP808':3,None:13},
            'supporting source provenance scope drift')
    for module,row in extras.items():
        if row.get('inherited_from') is not None:
            old = signed_publications['riemann-r-counted-residual-inverse']['additional_paid'][module]
            require({k:v for k,v in row.items() if k not in ('object','inherited_from')}
                    =={k:v for k,v in old.items() if k not in ('object','inherited_from')}
                    and row['object']['sha256']==old['object']['sha256'],f'supporting owner drift {module}')
    for module,row in (parents|extras).items():
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
            old, = [r for r in read(authority)['added_rows'] if r['module']==module]
            require(tracked(repo,stage['foundation_commit'],authority)==row['authority']['sha256']
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
    return parents|extras


def verify_cost(stage, inputs, package):
    construction = read(exact(stage['construction_cost']))
    rows = construction['attempts']
    require(construction['total_lean_calls']==len(rows)==36 and construction['failed_calls']==22 and
            construction['old_source_calls']==construction['old_source_successes']==0 and
            abs(construction['total_seconds']-sum(r['elapsed_seconds'] for r in rows))<1e-9,'construction cost drift')
    require(all(row['exit_code']>=0 for row in rows)
            and sum(row['exit_code']>0 for row in rows)==22
            and sum(row['exit_code']==0 for row in rows)==14
            and Counter(row['classification'] for row in rows)==
            {'new-science':32,'elaboration-diagnostic':3,'raw-inventory':1},'construction exit accounting drift')
    for row in rows:
        path = exact(row['receipt'])
        receipt = read(path)
        log = path.with_name(path.name.replace('.receipt.json','.log'))
        require(receipt['exit_code']==row['exit_code'] and receipt['elapsed_seconds']==row['elapsed_seconds']
                and receipt['old_compilations']==0 and receipt['lean_path_sha256']==stage['lean_path']['sha256']
                and receipt['source_sha256']==sha(receipt['source_snapshot']) and receipt['log_sha256']==sha(log),
                f'construction evidence drift {path.name}')
    raw = read(exact(stage['raw_inventory_receipt']))
    require(raw['exit_code']==0 and raw['command'][-5:]==[f'{a}-{b}' for a,b in ATTEMPTS],'raw inventory call drift')
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
            require(row['config_snapshot']==receipt['config_snapshot']
                    and exact(row['config_snapshot']).stat().st_size==receipt['config']['bytes']
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
                    'CP809_GATE_PASS positive=6 negative=1' in log.read_text().splitlines(),
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
    require(inputs['stage_map']['sha256']==STAGE_SHA and stage['schema']=='cp809-frozen-stage/v1'
            and stage['frozen'] and not stage['refreshed_old_sources'] and view.samefile(args.base_lean_path_file)
            and roots[0].samefile(args.compiled_root) and roots[0]==Path(stage['compiled_root']),'frozen view drift')
    parents = verify_paid(args.repo,stage,inputs,roots)
    verify_cost(stage,inputs,package)
    raw = read(exact(stage['raw_ci_inventory']))
    config = inputs['audit_config']
    new,owners = stage['inputs'],config['modules']
    require(raw['regions_read']==len(raw['rows'])==len(new)==len(owners)==5
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
    require(len(flat)==238 and len(runtime)==1 and set(runtime)=={name for name,ci in flat.items() if ci['partial']},
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
    require(report['schema']=='cp809-raw-first-private-body-audit/v1' and report['accepted']
            and report['raw_CIs']==238 and report['logical_CIs']==237 and report['compiler_extras']==1235
            and report['kernel_calls']==expected['kernel_calls']
            and len(report['inherited_full_CIs'])==expected['inherited']
            and report['axiom_closure']==expected['axiom_closure'] and set(report['axioms'])==AXIOMS
            and report['old_source_replays']==0 and report['subject_free_base_imports']==1
            and report['candidate_environment_imports']==0 and report['source_target_reads']==[],
            'kernel scope, closure, or axiom drift')
    require(report['body_edges']==config['bodyEdges'] and report['type_edges']==config['typeEdges']
            and [r['name'] for r in report['mouths']]==[row[0] for row in config['mouths']]
            and len(report['paid_CIs'])==len(config['paidSource'])==expected['paid_source_CIs']
            and len(report['paid_selected'])==88 and len(report['public_mouth_axioms'])==expected['public_mouths']
            and all(set(row['axioms'])<=AXIOMS for row in report['public_mouth_axioms'])
            and report['source_exclusions']==config['exclusions']
            and report['axiom_traversal']=='single-forward-scan-reverse-reachability',
            'producer or original consumer DAG drift')
    runtime = {row['name']:row for row in report['compiler_runtime_CIs']}
    require(set(runtime)==set(stage['compiler_runtime']) and len(runtime)==1,
            'audited compiler companion scope drift')
    for name,row in runtime.items():
        expected_runtime = stage['compiler_runtime'][name]
        require(row['parent']==expected_runtime['parent'] and row['incoming']==[name]
                and row['partial'] and not row['unsafe'] and row['kind']=='definition',
                f'audited compiler companion drift {name}')
    require(len(report['declarations'])==237
            and sum(r['name'].startswith('_private.') for r in report['declarations'])==168,
            'private logical CI drift')
    regenerated = report['inductive_generated_CIs']
    require(len(regenerated)==expected['inductive_generated']==4
            and Counter(row['kind'] for row in regenerated)=={'constructor':3,'recursor':1}
            and all(row['regenerated_in_inductive_block'] and row['same_full_CI'] for row in regenerated)
            and report['kernel_calls']+len(regenerated)+len(report['inherited_full_CIs'])==237,
            'regenerated Stage CI scope drift')
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
    require(manifest['checkpoint']=='CP809' and set(members)==PACKAGE_FILES,
            'published package scope drift')
    for name,row in members.items():
        path = package/name
        require(path.stat().st_size==row['bytes'] and sha(path)==row['sha256'],
                f'published package member drift {name}')
    cert = read(package/'certificate.json')
    require(cert['checkpoint']=='CP809' and cert['verdict']=='certified'
            and cert['inputs_sha256']==members['inputs.json']['sha256']
            and cert['audit_summary_sha256']==members['audit-summary.json']['sha256']
            and cert['independent_cost_sha256']==members['independent-cost.json']['sha256'],
            'certificate member drift')


def control_rows(log):
    prefix = 'CP809_CONTROL '
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
          raw_CIs=238,logical_CIs=237,private_logical_CIs=168,compiler_runtime_CIs=1,compiler_extras=1235,
          inductive_generated_CIs=len(report['inductive_generated_CIs']),
          kernel_calls=report['kernel_calls'],inherited_full_CIs=len(report['inherited_full_CIs']),
          independent_lean_calls=0 if args.verify_inputs_only else 2,old_source_recompiles=0,old_ci_replays=0)))


if __name__=='__main__':
    main()
