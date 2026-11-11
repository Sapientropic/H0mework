#!/usr/bin/env python3
"""Verify the exact CP528 original paid Step and Goldbach address sources and replay their new proofs."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

FLAGS = ['--trust=0', '-DElab.async=false', '-DwarningAsError=true',
         '-j1', '-M32000', '-DstderrAsMessages=false']

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    with path.open('rb') as data:
        return hashlib.file_digest(data, 'sha256').hexdigest()

def read(path):
    return json.loads(path.read_text())

def save(path, value):
    with path.open('x') as handle:
        handle.write(json.dumps(value, indent=2) + '\n')

def selected(module, roots):
    relative = Path(module.replace('.', '/') + '.olean')
    for index, root in enumerate(roots):
        path = root / relative
        if path.is_file():
            return path, index
    raise RuntimeError('Missing selected module ' + module)

def verified_compile(row, science):
    require(row['source_sha256'] == science['source_sha256'] and
            row['object_sha256'] == science['artifact_sha256'] and
            row['receipt_sha256'] == science['strict_receipt_sha256'] and
            row['exit_code'] == 0 and row['trust'] == 0 and
            row['werror'] and not row['elab_async'], 'Strict receipt drift ' + science['module'])

def verify_inputs(package, args):
    inputs = read(package/'inputs.json')
    roots = list(map(Path, args.base_lean_path_file.read_text().strip().split(os.pathsep)))
    require(roots and args.compiled_root.resolve() == roots[0].resolve(), 'Compiled view must be first')
    base = roots[0].parent
    require((args.repo/'Lean/lean-toolchain').read_text().strip() == inputs['lean_toolchain'],
            'Toolchain drift')
    for name, digest in inputs['local_evidence_sha256'].items():
        require(sha(package/name) == digest, 'Checker or evidence drift ' + name)
    for name, digest in inputs['frozen_inputs'].items():
        path = args.base_lean_path_file if name == 'lean-path.txt' else base/name
        require(sha(path) == digest, 'Frozen input drift ' + name)
    frozen = read(base/'stage-map.json')
    require(frozen['frozen'], 'Science map is unfrozen')
    science = {row['module']: row for row in inputs['science']}
    stages = {row['module']: row for row in frozen['inputs']}
    strict = {row['module']: row for row in read(package/'evidence/science-compiles.json')['rows']}
    require(science.keys() == stages.keys() == strict.keys(), 'Science owner scope drift')
    actual = []
    for module, row in science.items():
        stage = stages[module]
        source = (args.source_root or args.repo/'Lean')/(module.replace('.', '/')+'.lean')
        artifact, index = selected(module, roots)
        require(sha(source) == row['source_sha256'] == stage['source_sha256'] and
                sha(artifact) == row['artifact_sha256'] == stage['object']['sha256'] and
                artifact.stat().st_size == row['artifact_bytes'] and index == 0,
                'Selected source or object drift ' + module)
        imports = re.findall(r'^import\s+(\S+)', source.read_text(), re.M)
        require(imports == row['base'] and all(not item.startswith('scratch.') for item in imports),
                'Production import scope drift ' + module)
        require(stage['receipt']['sha256'] == row['strict_receipt_sha256'], 'Frozen receipt drift ' + module)
        verified_compile(strict[module], row)
        actual.append({**row, 'selected_olean': str(artifact), 'search_path_index': index})

    paid = read(package/'evidence/paid-parents.json')
    step, coverage = paid['parent'], paid['coverage']
    parents = [step['module'], coverage['module']]
    for row, source, commit in ((step, paid['source'], paid['tracked_commit']),
                               (coverage, coverage['source'], coverage['tracked_commit'])):
        source_path = 'Lean/' + row['module'].replace('.', '/') + '.lean'
        blob = subprocess.check_output(['git', 'show', f'{commit}:{source_path}'], cwd=args.repo)
        artifact, _ = selected(row['module'], roots)
        require(sha(args.repo/source_path) == hashlib.sha256(blob).hexdigest() == source['sha256'] and
                sha(artifact) == row['object']['sha256'] and artifact.stat().st_size == row['object']['bytes'],
                'Selected paid source or object drift ' + row['module'])
    for dep in step['inherited_selected_dependencies']:
        artifact, _ = selected(dep['module'], roots)
        require(sha(artifact) == dep['object']['sha256'] and artifact.stat().st_size == dep['object']['bytes'],
                'CP397 inherited object drift ' + dep['module'])
    for row in inputs['paid_signatures']:
        certificate = args.repo/row['certificate']
        require(sha(certificate) == row['certificate_sha256'], 'Paid certificate drift')
        prior_inputs = certificate.parent/'inputs.json'
        signed = read(certificate)
        require(signed['verdict'] == 'certified' and sha(prior_inputs) == signed['inputs']['sha256'],
                'Paid signed inputs drift')
        old = read(prior_inputs)
        if row['checkpoint'] == 'CP397':
            name = 'evidence/paid-parents.json'
            parent_evidence = certificate.parent/name
            require(sha(parent_evidence) == old['local_evidence_sha256'][name] == paid['prior_binding']['sha256'],
                    'CP397 recorded parent drift')
            prior_step = next(item for item in read(parent_evidence)['rows'] if item['module'] == step['module'])
            require(all(prior_step[key] == step[key] for key in ('source_sha256','object','receipt','input')),
                    'CP397 strict source, object or receipt drift')
        else:
            prior_compile = read(certificate.parent/'evidence/science-compile.json')
            require(old['science']['module'] == coverage['module'] and
                    old['science']['source_sha256'] == coverage['source']['sha256'] and
                    old['science']['object_sha256'] == coverage['object']['sha256'] and
                    prior_compile['receipt_sha256'] == coverage['strict_receipt']['sha256'] and
                    prior_compile['exit_code'] == 0, 'CP527 Coverage strict input drift')
    require(inputs['audit_group']['modules'] == list(science) and
            inputs['audit_group']['base'] == parents and
            {dep for row in science.values() for dep in row['base'] if dep not in science} == set(parents),
            'Replay scope includes an unintended owner')
    return inputs, roots, actual

def validate_audit(report, inputs, package):
    require(report['accepted'] and len(report['stages']) == 1, 'Independent replay did not close')
    stage = report['stages'][0]
    counts = inputs['expected']
    require(stage['raw'] == counts['raw'] and stage['kernel_calls'] == counts['kernel_calls'] and
            stage['safe_private'] == report['safe_private_original_CIs'] == counts['safe'] and
            sum(row['name'].startswith('_private.') for row in stage['declarations']) == counts['private'] and
            stage['compiler_extras'] == counts['compiler_extras'] and
            not stage['inherited'] and not stage['duplicates'] and not stage['base_has_unverified_sources'],
            'Independent replay left the new owner scope')
    companions = read(package/'evidence/compiler-companions.json')['excluded']
    found = stage['compiler_runtime']
    require(len(found) == len(companions) == counts['compiler_runtime'] and
            {(row['name'],row['owner']) for row in found} ==
            {(row['name'],row['module']) for row in companions} and
            all(not row['isUnsafe'] and row['isPartial'] and row['self_edges'] == 1 and
                row['nonself_incoming_edges'] == 0 and row['type_preserved'] and row['value_preserved']
                for row in found), 'Compiler companion scope drift')
    require([row['module'] for row in stage['modules']] == inputs['audit_group']['modules'],
            'Replayed owner order drift')
    require(len(report['public_mouths']) == counts['mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'], 'Source binding drift')
    require(set(report['axioms']) == {'propext','Classical.choice','Quot.sound'}, 'Axiom closure drift')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('repo','compiled-root','base-lean-path-file','output'):
        parser.add_argument('--'+option, type=Path, required=True)
    parser.add_argument('--source-root', type=Path)
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--verify-inputs-only', action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    inputs, roots, actual = verify_inputs(package, args)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    save(output/'provenance.json', {
        'schema':'cp528-provenance/v1','science':actual,'inputs_sha256':sha(package/'inputs.json'),
        'formal_sources':args.source_root is None,'paid_project_parents':2,'old_ci_replays':0,
        'old_source_recompiles':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
                          'formal_sources':args.source_root is None,'paid_project_parents':2,'lean_calls':0}))
        return

    lean = args.lean or Path(subprocess.check_output(['elan','which','lean'],
                   cwd=args.repo/'Lean',text=True).strip())
    env = {**os.environ, 'LEAN_PATH':os.pathsep.join(map(str, roots)),
           'LEAN_SYSROOT':str(lean.parent.parent)}
    calls = []
    def run(label, command, source):
        log = output/(label+'.log')
        start = time.monotonic()
        with log.open('xb') as out:
            process = subprocess.Popen(command,cwd=package,env=env,stdout=out,stderr=subprocess.STDOUT)
            print(json.dumps({'label':label,'pid':process.pid}),flush=True)
            code = process.wait()
        row = {'label':label,'command':command,'exit_code':code,'elapsed_seconds':time.monotonic()-start,
               'source_sha256':sha(source),'log_sha256':sha(log)}
        calls.append(row)
        save(output/(label+'.receipt.json'),row)
        if code:
            save(output/'cost.json',{'calls':calls,'old_ci_replays':0,'science_source_recompiles':0})
            raise RuntimeError(log.read_text()[-7000:])
    gate = package/'Gate.lean'
    run('gate',[str(lean),*FLAGS,'-DmaxErrors=8','--root='+str(package),'-o',str(output/'Gate.olean'),str(gate)],gate)
    controls = read(package/'evidence/typed-controls.json')['controls']
    marks = re.findall(r'^CP528_CONTROL ([+-]) (\w+)$',(output/'gate.log').read_text(),re.M)
    require(marks == [(row['sign'],row['name']) for row in controls], 'Typed controls drift')
    audit = package/'Audit.lean'
    config = output/'audit-config.json'
    body = output/'private-bodies.json'
    save(config,{'entry':inputs['entry'],'stages':[inputs['audit_group']],'output':str(body),
                 'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('audit',[str(lean),*FLAGS,'-DmaxErrors=1','--run',str(audit),str(config)],audit)
    report = read(body)
    validate_audit(report, inputs, package)
    save(output/'cost.json',{'calls':calls,'old_ci_replays':0,'science_source_recompiles':0})
    save(output/'certificate.json',{'schema':'cp528-reproduction/v1','verdict':'certified',
        'safe_private_original_CIs':report['safe_private_original_CIs'],'axioms':report['axioms'],
        'inputs_sha256':sha(package/'inputs.json'),'body_report_sha256':sha(body),
        'typed_controls':controls,
        'cost_sha256':sha(output/'cost.json')})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}))

if __name__ == '__main__':
    main()
