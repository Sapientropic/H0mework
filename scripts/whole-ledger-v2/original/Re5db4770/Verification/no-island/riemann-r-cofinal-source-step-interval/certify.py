#!/usr/bin/env python3
"""Verify the CP531 actual source Step interval, mapped Joint block and complete consumer."""
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
    require(paid['schema'] == 'r-cofinal-source-step-interval-parents/v1' and
            sorted(r['checkpoint'] for r in parents) == ['CP515','CP530','CP530','paid original pair Transport'],
            'paid parent scope drift')
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(imports == {row['module'] for row in parents} == set(inputs['audit_base']),
            'direct paid context drift')
    for row in parents:
        module = row['module']
        source = args.repo/'Lean'/(module.replace('.', '/')+'.lean')
        artifact, _ = selected(module,roots)
        require(sha(source) == row['source']['sha256'] and sha(artifact) == row['object']['sha256'],
                'paid source/body drift '+module)
        strict_path = Path(row['strict_receipt']['path'])
        strict = read(strict_path)
        require(sha(strict_path) == row['strict_receipt']['sha256'] and strict['exit_code'] == 0 and
                {'--trust=0','-DwarningAsError=true','-DElab.async=false'} <= set(strict['command']),
                'strict paid receipt drift '+module)
        if row['checkpoint'] == 'paid original pair Transport':
            require(strict['sha256'] == row['source']['sha256'] and strict['olean_sha256'] == row['object']['sha256'],
                    'original Pair.Transport strict scope drift')
        else:
            require(strict['module'] == module and
                    (strict['source']['sha256'],strict['object']['sha256']) ==
                    (row['source']['sha256'],row['object']['sha256']), 'paid strict body drift '+module)
            publication = Path(row['publication']['path'])
            require(sha(publication) == row['publication']['sha256'] and read(publication)['commit'] == row['tracked_commit'],
                    'paid publication drift '+module)
            name = 'riemann-r-cofinal-source-request-origin' if row['checkpoint']=='CP530' else 'goldbach-fixed-actor-receipt-segment'
            signed = args.repo/'Verification/no-island'/name
            cert = read(signed/'certificate.json')
            prior_inputs = signed/'inputs.json'
            require(cert['verdict'] == 'certified' and sha(signed/'certificate.json') == read(publication)['certificate_sha256'] and
                    sha(prior_inputs) == cert['inputs']['sha256'], 'paid certificate drift '+module)
            prior = read(prior_inputs)
            owner = next(item for item in prior['science'] if item['module'] == module)
            require((owner['source_sha256'],owner['artifact_sha256']) ==
                    (row['source']['sha256'],row['object']['sha256']) and
                    prior['frozen_inputs']['stage-map.json'] == row['stage_map']['sha256'], 'paid owner drift '+module)
            if row['checkpoint']=='CP515':
                compiles = read(signed/'evidence/science-compiles.json')
                focused = next(item for item in compiles['stages'] if item['module'] == module)
                require(focused['receipt_sha256'] == sha(strict_path), 'recovered SegmentRead receipt drift')
        for dep in row['inherited_selected_dependencies']:
            hit, _ = selected(dep['module'],roots)
            require(hit.samefile(dep['origin']), 'paid inherited first hit drift '+dep['module'])
    require(stage['raw_ci_inventory']['sha256'] == inputs['frozen_inputs']['raw-inventory.json'], 'frozen inventory drift')
    block = read(package/'evidence/block-input-binding.json')
    old_interval = args.repo/'Verification/no-island/riemann-r-cofinal-receipt-interval-fibre/certificate.json'
    require(sha(old_interval) == block['legacy_interval_certificate_sha256'] and
            sha(args.repo/block['legacy_interval_source']) == block['legacy_interval_source_sha256'] and
            actual[-1]['source_sha256'] == block['actual_source_sha256'] and
            block['membership_consumes_paired_block'], 'original mapped block input drift')
    old_module = block['legacy_interval_source'].removeprefix('Lean/').removesuffix('.lean').replace('/','.')
    old_object, _ = selected(old_module,roots)
    require(sha(old_object) == block['legacy_interval_object_sha256'], 'paid literal interval body drift')
    prior_control = inputs['paid_duplicate_control']
    prior = args.repo/'Verification/no-island/riemann-r-cofinal-source-request-origin'
    old_controls = prior/'evidence/typed-controls.json'
    require(sha(prior/'certificate.json') == prior_control['certificate_sha256'] and
            sha(old_controls) == prior_control['typed_controls_sha256'] and
            ['-',prior_control['control']] in read(old_controls)['controls'], 'paid duplicate control drift')
    fixture = read(package/'evidence/paid-fixture.json')
    old = args.repo/'Verification/no-island/riemann-r-cofinal-receipt-position'
    controls = old/'evidence/typed-controls.json'
    focus = read(controls)['focused_result']
    require(sha(old/'certificate.json') == fixture['certificate_sha256'] and
            sha(controls) == read(old/'certificate.json')['typed_controls']['sha256'] and
            focus['object_sha256'] == fixture['object_sha256'] and focus['receipt_sha256'] == fixture['receipt_sha256'] and
            fixture['logical_module_components'] == ['002-gate.source'] and
            sha(Path(fixture['archive'])) == fixture['archive_sha256'], 'paid exact Step fixture drift')
    return inputs, roots, actual, fixture


def extract_fixture(output, fixture):
    root = output/'fixture-lib'
    root.mkdir()
    target = root/'002-gate.source.olean'
    with target.open('xb') as out, subprocess.Popen(
            ['zstd','-dc',fixture['archive']],stdout=subprocess.PIPE) as packed:
        try:
            subprocess.run(['tar','-xOf','-',fixture['member']],stdin=packed.stdout,stdout=out,check=True)
        finally:
            packed.stdout.close()
        require(packed.wait() == 0, 'paid fixture archive decode failed')
    require(sha(target) == fixture['object_sha256'] and target.stat().st_size == fixture['object_bytes'],
            'restored paid fixture changed')
    return root


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['inherited'] == stage['duplicates'] == 0 and
            not stage['base_has_unverified_sources'] and not stage['compiler_runtime'] and
            report['fresh_raw_regions'] == 3 and report['paid_base_environment_imports'] == 1 and
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
    inputs, roots, actual, fixture = verify_inputs(package,args)
    output = args.output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    save(output/'provenance.json',{'schema':'cp531-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_project_parents':4,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_project_parents':4,'lean_calls':0}))
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
        save(cost,{'schema':'cp531-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    def compile_gate(label, filename, scope_env):
        return run(label,filename,[str(lean),*FLAGS,'--root='+str(package),
            '-o',str(output/(filename+'.olean')),str(package/filename)],scope_env)

    fixture_root = extract_fixture(output,fixture)
    canonical = output/'canonical-application.json'
    gate = compile_gate('001-gate','Gate.lean',{
        **env,'LEAN_PATH':str(fixture_root)+os.pathsep+env['LEAN_PATH'],
        'CP531_CANONICAL_REPORT':str(canonical),'CP531_CANONICAL_CURRENT':str(output/'canonical-current.json')})
    markers = [list(x) for log in (gate,) for x in re.findall(r'^CP531_CONTROL ([+-]) (\w+)$',log.read_text(),re.M)]
    require(markers == inputs['typed_controls'],'typed controls drift')
    direct = read(canonical)
    require(direct['accepted'] and direct['new_proof_premises'] == direct['Meta_calls'] == 0 and
            direct['kernel_add_decl_calls'] == 1 and direct['conjoined_claims'] == inputs['canonical_claims'],
            'literal canonical method application drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'new-cofinal-source-step-interval-owners','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp531-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],'report_sha256':sha(raw),
        'canonical_application_sha256':sha(canonical),'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
