#!/usr/bin/env python3
"""Verify the CP521 ordered receipt block and its same-method actual boundary consumer."""
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
    require(paid['schema'] == 'cp521-exact-paid-source-parents/v1' and paid['lean_calls'] == 0 and
            len(paid['rows']) == 4, 'paid source parent scope drift')
    direct = {x['module'] for x in paid['rows'] if not x['paid']['transitive_import']}
    all_imports = {m for row in science.values() for m in row['base'] if m not in science}
    require(direct == all_imports and len(direct) == 2,
            'direct project parent coverage drift')
    for row in paid['rows']:
        module = row['module']
        artifact, _ = selected(module, roots)
        require(sha(args.repo/row['repo_path']) == row['source_sha256'] and
                sha(artifact) == row['object_sha256'], 'paid parent source/body drift '+module)
        evidence = args.repo/row['evidence']
        require(sha(evidence) == row['evidence_sha256'], 'paid parent evidence drift '+module)
        old = read(evidence)
        kind = row['paid']['kind']
        if kind in ('CP514-independent-signoff', 'CP506-independent-signoff'):
            prior_inputs = evidence.parent/'inputs.json'
            require(old['verdict'] == 'certified' and sha(prior_inputs) == old['inputs']['sha256'],
                    'prior certificate input drift '+module)
            prior = next(x for x in read(prior_inputs)['science'] if x['module'] == module)
            binding = (prior['source_sha256'], prior['artifact_sha256'])
        else:
            require(kind == 'CP339-certified-canonical-binding' and row['paid']['exit_code'] == 0,
                    'unrecognized paid authority '+module)
            prior = next(x for x in old['canonical_sources'] if x['module'] == module)
            binding = (prior['source_sha256'], prior['olean_sha256'])
        require(binding == (row['source_sha256'], row['object_sha256']), 'prior signed body drift '+module)
    require(inputs['audit_group']['modules'] == list(science) and set(inputs['audit_group']['base']) == all_imports,
            'grouped replay changed subject/base scope')
    return inputs, roots, actual


def validate_report(output, inputs, actual):
    report = read(output/'private-bodies.json')
    require(len(report['stages']) == 1, 'grouped replay scope changed')
    stage = report['stages'][0]
    require(stage['inherited'] == stage['duplicates'] == 0 and not stage['base_has_unverified_sources'] and
            not stage['compiler_runtime'] and stage['kernel_calls'] == inputs['expected_raw_CIs'],
            'replay escaped new safe CI scope')
    owners = {row['module']: row for row in actual}
    for row in stage['modules']:
        module = row['module']
        owner = owners.pop(module)
        require(sha(row['selected_olean']) == owner['artifact_sha256'] and row['raw'] == owner['raw_CIs'] and
                row['compiler_extras'] == owner['compiler_extras'], 'replayed owner drift '+module)
    require(not owners and report['accepted'] and
            report['safe_private_original_CIs'] == stage['raw'] == inputs['expected_raw_CIs'] and
            sum(x['name'].startswith('_private.') for x in stage['declarations']) == inputs['expected_private_CIs'] and
            stage['compiler_extras'] == inputs['expected_compiler_extras'] and
            len(report['public_mouths']) == inputs['expected_public_mouths'] and
            len(report['source_body_bindings']) == inputs['expected_source_body_bindings'] and
            report['block_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete exact proof and provenance inventory')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('repo', 'compiled-root', 'base-lean-path-file', 'output'):
        parser.add_argument('--'+option, type=Path, required=True)
    parser.add_argument('--source-root', type=Path)
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--verify-inputs-only', action='store_true')
    parser.add_argument('--resume-audit', metavar='REPORT_SHA256')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    inputs, roots, actual = verify_inputs(package, args)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    save(output/'provenance.json', {
        'schema': 'cp521-provenance/v1', 'science': actual, 'inputs_sha256': sha(package/'inputs.json'),
        'formal_sources': args.source_root is None, 'paid_project_parents': 4,
        'old_ci_replays': 0, 'old_source_recompiles': 0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict': 'exact-inputs-verified', 'science': len(actual),
                          'formal_sources': args.source_root is None, 'paid_project_parents': 4, 'lean_calls': 0}))
        return

    lean = args.lean or Path(subprocess.check_output(
        ['elan', 'which', 'lean'], cwd=args.repo/'Lean', text=True).strip())
    env = {**os.environ, 'LEAN_SYSROOT': str(lean.parent.parent),
           'PATH': str(lean.parent)+os.pathsep+os.environ.get('PATH', ''),
           'LEAN_PATH': os.pathsep.join(map(str, roots)),
           'CP521_CANONICAL_REPORT': str(output/'canonical-application.json'),
           'CP521_CANONICAL_CURRENT': str(output/'canonical-current.json')}
    cost = output/'cost.json'
    calls = read(cost)['calls'] if cost.exists() else []

    def run(label, command, source, config=None):
        tag = f'{len(calls)+1:03d}-'+label
        log = output/(tag+'.log')
        snapshot = output/(tag+'.source.lean')
        snapshot.write_bytes(source.read_bytes())
        running = output/(tag+'.running.json')
        started = time.monotonic()
        with log.open('wb') as stream:
            child = subprocess.Popen(command, cwd=package, env=env, stdout=stream,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            save(running, {'pid': child.pid, 'command': command})
            print(json.dumps({'label': tag, 'pid': child.pid}), flush=True)
            code = child.wait()
            stream.flush()
            os.fsync(stream.fileno())
        row = {'label': tag, 'exit_code': code, 'elapsed_seconds': time.monotonic()-started,
               'source_sha256': sha(snapshot), 'log_sha256': sha(log),
               'config_sha256': sha(config) if config is not None else None}
        calls.append(row)
        save(output/(tag+'.receipt.json'), row)
        running.unlink()
        save(cost, {'schema': 'cp521-independent-cost/v1', 'calls': calls, 'actual_calls': len(calls),
                    'known_seconds': sum(x['elapsed_seconds'] for x in calls), 'unknown_calls': 0,
                    'old_ci_replays': 0, 'science_source_recompiles': 0})
        if code:
            print(log.read_text()[-7000:], flush=True)
            raise SystemExit(code)
        return log

    if args.resume_audit:
        require(sha(output/'private-bodies.json') == args.resume_audit, 'paid audit report changed')
        successes = [x for x in calls if x['exit_code'] == 0 and x['label'].endswith('-audit') and
                     x['source_sha256'] == sha(package/'Audit.lean') and
                     sha(output/(x['label']+'.log')) == x['log_sha256'] and
                     'PASS new-safe-private=77' in (output/(x['label']+'.log')).read_text()]
        require(len(successes) == 1, 'exact successful audit receipt not unique')
    else:
        require(not calls, 'use a clean output or explicitly resume a paid audit')
        config = output/'audit-config.json'
        save(config, {'entry': inputs['entry'], 'stages': [inputs['audit_group']],
                      'output': str(output/'private-bodies.json'), 'progress': str(output/'ci-progress.jsonl'),
                      'current': str(output/'current-ci.json')})
        run('audit', [str(lean), *FLAGS, '--run', str(package/'Audit.lean'), str(config)],
            package/'Audit.lean', config)

    report = validate_report(output, inputs, actual)
    (output/'canonical-application.json').unlink(missing_ok=True)
    (output/'canonical-current.json').unlink(missing_ok=True)
    log = run('gate', [str(lean), *FLAGS, '--root='+str(package), '-o', str(output/'Gate.olean'),
                       str(package/'Gate.lean')], package/'Gate.lean')
    markers = re.findall(r'^CP521_CONTROL ([+-]) (\w+)$', log.read_text(), re.M)
    require([list(row) for row in markers] == inputs['typed_controls'], 'typed control scope drift')
    canonical = read(output/'canonical-application.json')
    require(canonical['accepted'] and canonical['new_proof_premises'] == canonical['Meta_calls'] == 0 and
            canonical['kernel_add_decl_calls'] == 1 and canonical['conjoined_claims'] == inputs['canonical_claims'],
            'literal same-method canonical application drift')
    verify_inputs(package, args)
    save(output/'certificate.json', {
        'schema': 'cp521-reproduction/v1', 'verdict': 'certified',
        'safe_private_original_CIs': report['safe_private_original_CIs'], 'axioms': report['axioms'],
        'typed_controls': inputs['typed_controls'], 'inputs_sha256': sha(package/'inputs.json'),
        'canonical_application_sha256': sha(output/'canonical-application.json'),
        'raw_body_report_sha256': sha(output/'private-bodies.json'), 'cost_sha256': sha(cost),
        'old_ci_replays': 0, 'whole_next_is_existing_same_method': True})
    print(json.dumps({'verdict': 'certified', 'certificate': str(output/'certificate.json')}), flush=True)


if __name__ == '__main__':
    main()
