#!/usr/bin/env python3
"""Verify the CP529 original absolute receipt Step and its same-method Joint and Model."""
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


def verify_inputs(package, args):
    inputs = read(package/'inputs.json')
    roots = list(map(Path, args.base_lean_path_file.read_text().strip().split(os.pathsep)))
    require(args.compiled_root.resolve() == roots[0].resolve(), 'complete compiled root must be first')
    require((args.repo/'Lean/lean-toolchain').read_text().strip() == inputs['lean_toolchain'], 'toolchain drift')
    for name, digest in inputs['local_evidence_sha256'].items():
        require(sha(package/name) == digest, 'checker/evidence drift '+name)
    for name in ('stage-map.json', 'context.json'):
        require(sha(roots[0].parent/name) == inputs['frozen_inputs'][name], 'frozen input drift '+name)
    require(sha(args.base_lean_path_file) == inputs['frozen_inputs']['lean-path.txt'], 'compiled view drift')

    stage = read(roots[0].parent/'stage-map.json')
    require(stage['frozen'], 'unfrozen science map')
    frozen = {row['module']: row for row in stage['inputs']}
    science = {row['module']: row for row in inputs['science']}
    strict = {row['module']: row for row in read(package/'evidence/science-compiles.json')['rows']}
    require(frozen.keys() == science.keys() == strict.keys(), 'science owner set drift')
    actual = []
    for module, row in science.items():
        source = ((args.source_root or args.repo/'Lean')/(module.replace('.', '/')+'.lean'))
        artifact, index = selected(module, roots)
        frozen_row = frozen[module]
        require(sha(source) == row['source_sha256'] == frozen_row['source_sha256'] and
                sha(artifact) == row['artifact_sha256'] == frozen_row['object']['sha256'] and
                artifact.stat().st_size == row['artifact_bytes'], 'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)', source.read_text(), re.M)
        require(imports == row['base'] and not any(x.startswith('scratch.') for x in imports), 'science import drift '+module)
        require(strict[module]['receipt_sha256'] == row['strict_receipt_sha256'] == frozen_row['receipt']['sha256'] and
                strict[module]['source_sha256'] == row['source_sha256'] and
                strict[module]['object_sha256'] == row['artifact_sha256'] and
                strict[module]['exit_code'] == 0 and strict[module]['trust'] == 0 and
                strict[module]['werror'] and not strict[module]['elab_async'],
                'strict source/body receipt drift '+module)
        actual.append({**row, 'selected_olean': str(artifact), 'search_path_index': index})


    paid = read(package/'evidence/paid-parents.json')
    require(paid['schema'] == 'r-cofinal-receipt-position-parents/v1', 'paid parent schema drift')
    parents = paid['parents']
    require(sorted(row['checkpoint'] for row in parents) == ['CP521','CP521','CP523','CP528'],
            'paid parent scope drift')
    pinned = inputs['pinned_dependency']
    pin_artifact, _ = selected(pinned['module'],roots)
    require(sha(pin_artifact) == pinned['object_sha256'], 'pinned Lean dependency drift')
    direct = {row['module'] for row in parents}
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(len(direct) == 4 and imports == direct | {pinned['module']}, 'direct import coverage drift')
    for row in parents:
        module = row['module']
        source = args.repo/'Lean'/(module.replace('.', '/')+'.lean')
        artifact, _ = selected(module,roots)
        require(sha(source) == row['source']['sha256'] and sha(artifact) == row['object']['sha256'],
                'paid source/object drift '+module)
        old_path = Path(row['certificate']['path'])
        certificate = args.repo/'Verification/no-island'/old_path.parent.name/'certificate.json'
        old_inputs = certificate.parent/'inputs.json'
        old = read(certificate)
        require(sha(certificate) == row['certificate']['sha256'] and old['verdict'] == 'certified' and
                sha(old_inputs) == old['inputs']['sha256'], 'prior certificate drift '+module)
        previous = read(old_inputs)
        prior = next(x for x in previous['science'] if x['module'] == module)
        require((prior['source_sha256'],prior['artifact_sha256']) ==
                (row['source']['sha256'],row['object']['sha256']) and
                previous['frozen_inputs']['stage-map.json'] == row['stage_map']['sha256'],
                'prior signed science drift '+module)
        receipt_path = Path(row['strict_receipt']['path'])
        receipt = read(receipt_path)
        require(sha(receipt_path) == row['strict_receipt']['sha256'] and receipt['exit_code'] == 0 and
                receipt['module'] == module and (receipt['source']['sha256'],receipt['object']['sha256']) ==
                (row['source']['sha256'],row['object']['sha256']), 'paid strict receipt drift '+module)
        for dependency in row['inherited_selected_dependencies']:
            hit, _ = selected(dependency['module'],roots)
            require(hit.samefile(dependency['origin']), 'paid inherited first-hit drift '+dependency['module'])
    require(inputs['audit_group']['modules'] == list(science) and set(inputs['audit_group']['base']) == imports,
            'grouped replay changed subject/base scope')
    require(stage['raw_ci_inventory']['sha256'] == inputs['frozen_inputs']['raw-inventory.json'],
            'frozen raw CI inventory drift')
    cross = stage['partition_direct_consumer']['goldbach_checks']
    require([row['stage'] for row in cross] == ['Shape','Address'], 'Goldbach direct-consumer scope drift')
    for row in cross:
        source = args.repo/row['intended_formal_path']
        artifact = Path(row['object']['path'])
        receipt_path = Path(row['strict_receipt']['path'])
        receipt = read(receipt_path)
        require(sha(source) == row['source']['sha256'] == receipt['source']['sha256'] and
                sha(artifact) == row['object']['sha256'] == receipt['object']['sha256'] and
                sha(receipt_path) == row['strict_receipt']['sha256'] and
                receipt['exit_code'] == 0 and receipt['source_unchanged'] and
                {'--trust=0','-DwarningAsError=true','-DElab.async=false'} <= set(receipt['command']),
                'Goldbach exact focused consumer drift '+row['stage'])
    require(cross[0]['source']['sha256'] != cross[0]['prior_source_sha256'] and
            cross[1]['source']['sha256'] == cross[1]['prior_source_sha256'],
            'Goldbach Shape revision or unchanged Address identity drift')
    return inputs, roots, actual

def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    require(report['accepted'] and stage['inherited'] == stage['duplicates'] == 0 and
            not stage['base_has_unverified_sources'], 'replay escaped the new owner scope')
    expected_owners = {r['module']:r for r in actual}
    for row in stage['modules']:
        owner = expected_owners.pop(row['module'])
        require(sha(row['selected_olean']) == owner['artifact_sha256'] and
                row['raw'] == owner['raw_CIs'] and row['compiler_extras'] == owner['compiler_extras'],
                'replayed owner drift '+row['module'])
    counts = inputs['counts']
    runtime, = stage['compiler_runtime']
    companion = counts['compiler_companion']
    require(runtime['name'] == companion['name'] and runtime['owner'] == companion['module'] and
            runtime['safe_source'] == runtime['name'].removesuffix('._unsafe_rec') and
            runtime['isPartial'] and not runtime['isUnsafe'] and
            runtime['self_edges'] == companion['self_edges'] == 1 and runtime['nonself_incoming_edges'] == 0 and
            runtime['type_preserved'] and runtime['value_preserved'], 'runtime companion isolation changed')
    require(not expected_owners and report['safe_private_original_CIs'] == stage['safe_private'] == counts['safe'] and
            stage['raw'] == counts['raw'] and stage['kernel_calls'] == counts['kernel_calls'] and
            sum(x['name'].startswith('_private.') for x in stage['declarations']) == counts['private'] and
            stage['compiler_extras'] == counts['extras'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['value_body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['position_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source and consumer provenance')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('repo','compiled-root','base-lean-path-file','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--source-root',type=Path)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--verify-inputs-only',action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    inputs, roots, actual = verify_inputs(package,args)
    output = args.output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    save(output/'provenance.json',{'schema':'cp529-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_project_parents':4,'old_ci_replays':0,'old_source_recompiles':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_project_parents':4,'lean_calls':0}))
        return

    lean = args.lean or Path(subprocess.check_output(['elan','which','lean'],cwd=args.repo/'Lean',text=True).strip())
    canonical = output/'canonical-application.json'
    env = {**os.environ,'LEAN_PATH':os.pathsep.join(map(str,roots)),'LEAN_SYSROOT':str(lean.parent.parent),
           'CP529_CANONICAL_REPORT':str(canonical),'CP529_CANONICAL_CURRENT':str(output/'canonical-current.json')}
    cost = output/'cost.json'
    require(not cost.exists(),'use an empty output directory for a fresh run')
    calls = []

    def run(label, source, command, config=None):
        log = output/(label+'.log')
        start = time.monotonic()
        with log.open('wb') as stream:
            child = subprocess.Popen(command,cwd=package,env=env,stdout=stream,stderr=subprocess.STDOUT)
            print(json.dumps({'label':label,'pid':child.pid}),flush=True)
            code = child.wait()
        row = {'label':label,'exit_code':code,'elapsed_seconds':time.monotonic()-start,
            'source_sha256':sha(source),'log_sha256':sha(log),'config_sha256':sha(config) if config else None}
        calls.append(row)
        save(output/(label+'.receipt.json'),row)
        save(cost,{'schema':'cp529-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = package/'Gate.lean'
    gate_log = run('001-gate',gate,[str(lean),*FLAGS,'--root='+str(package),'-o',str(output/'Gate.olean'),str(gate)])
    markers = re.findall(r'^CP529_CONTROL ([+-]) (\w+)$',gate_log.read_text(),re.M)
    require([list(row) for row in markers] == inputs['typed_controls'],'typed control scope drift')
    direct = read(canonical)
    require(direct['accepted'] and direct['new_proof_premises'] == direct['Meta_calls'] == 0 and
            direct['kernel_add_decl_calls'] == 1 and direct['conjoined_claims'] == inputs['canonical_claims'],
            'literal canonical method application drift')
    audit = package/'Audit.lean'
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'entry':inputs['entry'],'stages':[inputs['audit_group']],'output':str(raw),
        'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit',audit,[str(lean),*FLAGS,'--run',str(audit),str(config)],config)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp529-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],'report_sha256':sha(raw),
        'canonical_application_sha256':sha(canonical),'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
