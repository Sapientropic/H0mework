#!/usr/bin/env python3
"""Verify the CP532 complete grouped source Steps and original Joint boundary."""
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
    parents = paid['parents']
    require(paid['schema'] == 'cofinal-complete-grouped-write-parents/v1' and
            len(parents) == 2 and all(row['checkpoint'] == 'CP531' for row in parents), 'paid parent scope drift')
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(imports == {row['module'] for row in parents} == set(inputs['audit_base']), 'direct paid context drift')
    authority = args.repo/'Verification/no-island/riemann-r-cofinal-source-step-interval'
    certificate = authority/'certificate.json'
    old_inputs = authority/'inputs.json'
    old = read(certificate)
    require(old['verdict'] == 'certified' and sha(old_inputs) == old['inputs']['sha256'], 'CP531 certificate input drift')
    prior = read(old_inputs)
    for row in parents:
        module = row['module']
        source = args.repo/'Lean'/(module.replace('.', '/')+'.lean')
        artifact, _ = selected(module,roots)
        require(sha(source) == row['source']['sha256'] and sha(artifact) == row['object']['sha256'],
                'paid source/body drift '+module)
        receipt_path = Path(row['strict_receipt']['path'])
        receipt = read(receipt_path)
        require(sha(receipt_path) == row['strict_receipt']['sha256'] and receipt['exit_code'] == 0 and
                receipt['module'] == module and {'--trust=0','-DElab.async=false','-DwarningAsError=true'} <= set(receipt['command']),
                'paid strict receipt drift '+module)
        record = next(item for item in prior['science'] if item['module'] == module)
        require(sha(certificate) == row['certificate']['sha256'] and
                (record['source_sha256'],record['artifact_sha256']) ==
                (receipt['source']['sha256'],receipt['object']['sha256']) ==
                (row['source']['sha256'],row['object']['sha256']) and
                prior['frozen_inputs']['stage-map.json'] == row['stage_map']['sha256'], 'paid owner drift '+module)
        publication = Path(row['publication']['path'])
        require(sha(publication) == row['publication']['sha256'] and
                read(publication)['commit'] == row['tracked_commit'] and
                read(publication)['certificate_sha256'] == row['certificate']['sha256'], 'paid publication drift '+module)
        for dep in row['inherited_selected_dependencies']:
            hit, _ = selected(dep['module'],roots)
            require(hit.samefile(dep['origin']), 'paid inherited first hit drift '+dep['module'])
    require(stage['raw_ci_inventory']['sha256'] == inputs['frozen_inputs']['raw-inventory.json'], 'frozen raw inventory drift')
    return inputs, roots, actual


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['inherited'] == stage['duplicates'] == 0 and
            not stage['base_has_unverified_sources'] and not stage['compiler_runtime'] and
            report['fresh_raw_regions'] == 2 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    owners = {r['module']:r for r in actual}
    for owner in stage['modules']:
        selected_owner = owners.pop(owner['module'])
        require(sha(owner['selected_olean']) == selected_owner['artifact_sha256'] and
                owner['raw'] == selected_owner['raw_CIs'] and owner['compiler_extras'] == selected_owner['compiler_extras'],
                'wrong audited owner '+owner['module'])
    require(not owners and report['safe_private_original_CIs'] == stage['raw'] == counts['safe'] and
            stage['kernel_calls'] == counts['kernel_calls'] and stage['compiler_extras'] == counts['extras'] and
            sum(r['name'].startswith('_private.') for r in stage['declarations']) == counts['private'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['source_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source provenance')
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
    save(output/'provenance.json',{'schema':'cp532-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_project_parents':2,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_project_parents':2,'lean_calls':0}))
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
        save(cost,{'schema':'cp532-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    def compile_gate(label, filename, scope_env):
        return run(label,filename,[str(lean),*FLAGS,'--root='+str(package),
            '-o',str(output/(filename+'.olean')),str(package/filename)],scope_env)

    canonical = output/'canonical-application.json'
    gate = compile_gate('001-gate','Gate.lean',{
        **env,
        'CP532_CANONICAL_REPORT':str(canonical),'CP532_CANONICAL_CURRENT':str(output/'canonical-current.json')})
    markers = [list(x) for log in (gate,) for x in re.findall(r'^CP532_CONTROL ([+-]) (\w+)$',log.read_text(),re.M)]
    require(markers == inputs['typed_controls'],'typed controls drift')
    direct = read(canonical)
    require(direct['accepted'] and direct['new_proof_premises'] == direct['Meta_calls'] == 0 and
            direct['kernel_add_decl_calls'] == 1 and direct['conjoined_claims'] == inputs['canonical_claims'],
            'literal canonical method application drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'new-cofinal-complete-grouped-write-owners','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp532-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],'report_sha256':sha(raw),
        'canonical_application_sha256':sha(canonical),'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
