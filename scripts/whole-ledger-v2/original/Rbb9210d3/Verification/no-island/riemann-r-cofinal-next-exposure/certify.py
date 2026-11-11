#!/usr/bin/env python3
"""Recheck the CP514 cofinal next exposure consumer against the fixed paid imports."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import time

FLAGS = ['--trust=0', '-DElab.async=false', '-DwarningAsError=true', '-DmaxErrors=1',
         '-j1', '-M32000', '-DstderrAsMessages=false']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    with pathlib.Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    return json.loads(pathlib.Path(path).read_text())


def save(path, value):
    with pathlib.Path(path).open('w') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def selected(module, roots):
    package = module.split('.')[0]
    for index, root in enumerate(map(pathlib.Path, roots)):
        if (root/package).is_dir() or (root/(package+'.olean')).is_file():
            path = root/(module.replace('.', '/')+'.olean')
            require(path.is_file(), 'selected package root lacks '+module)
            return path, index
    raise RuntimeError('missing '+module)


def verify_inputs(package, args):
    inputs = read(package/'inputs.json')
    roots = args.base_lean_path_file.read_text().strip().split(os.pathsep)
    require(str(args.compiled_root.resolve()) == str(pathlib.Path(roots[0]).resolve()),
            'complete compiled-root must be the first provider')
    require((args.repo/'Lean/lean-toolchain').read_text().strip() == inputs['lean_toolchain'],
            'toolchain drift')
    for filename, expected in inputs['local_evidence_sha256'].items():
        require(sha(package/filename) == expected, 'checker/evidence drift '+filename)

    source_root = args.source_root or args.repo/'Lean'
    actual = []
    science = {row['module']: row for row in inputs['science']}
    for module, row in science.items():
        source = source_root/(module.replace('.', '/')+'.lean')
        artifact, index = selected(module, roots)
        require(sha(source) == row['source_sha256'] and sha(artifact) == row['artifact_sha256'],
                'fixed science source/body mismatch '+module)
        imports = re.findall(r'^import\s+(\S+)', source.read_text(), re.M)
        require(imports == row['base'] and not any(x.startswith('scratch.') for x in imports),
                'science import drift '+module)
        actual.append({**row, 'selected_olean': str(artifact), 'search_path_index': index})

    paid = read(package/'evidence/paid-parents.json')
    require(paid['schema'] == 'cp514-preflight-paid-parents/v1' and paid['lean_calls'] == 0,
            'paid parent record drift')
    direct = {x['module'] for x in paid['rows'] if not x['paid']['transitive_import']}
    imported = {m for row in science.values() for m in row['base']} - science.keys()
    require(direct == {m for m in imported if m.startswith('SaturationMonoid.')} and
            len(direct) == len(paid['rows']) == 4, 'direct paid project parent drift')
    require({x['module'] for x in inputs['stdlib_imports']} == imported - direct,
            'direct stdlib coverage drift')
    for row in inputs['stdlib_imports']:
        artifact, _ = selected(row['module'], roots)
        require(sha(artifact) == row['artifact_sha256'], 'stdlib import artifact drift '+row['module'])
    for row in paid['rows']:
        module = row['module']
        artifact, _ = selected(module, roots)
        require(row['paid']['exit_code'] == 0 and sha(args.repo/row['repo_path']) ==
                row['source_sha256'] and sha(artifact) == row['object_sha256'],
                'current paid parent source/object drift '+module)
        evidence_path = args.repo/row['evidence']
        require(sha(evidence_path) == row['evidence_sha256'], 'paid authority drift '+module)
        evidence = read(evidence_path)
        kind = row['paid']['kind']
        if kind == 'CP506-independent-signoff':
            bound_inputs = evidence_path.parent/'inputs.json'
            require(sha(bound_inputs) == evidence['inputs']['sha256'], 'paid CP506 inputs drift')
            old = next(x for x in read(bound_inputs)['science'] if x['module'] == module)
            binding = (old['source_sha256'], old['artifact_sha256'])
        elif kind == 'CP506-inherited-CP397-exact-step':
            old = next(x for x in evidence['direct_paid_parents'] if x['module'] == module)
            binding = (old['source']['sha256'], old['selected_object']['sha256'])
        elif kind == 'CP339-certified-canonical-binding':
            old = next(x for x in evidence['canonical_sources'] if x['module'] == module)
            binding = (old['source_sha256'], old['olean_sha256'])
        elif kind == 'CP394-397-independent-exact-first-hit':
            old = next(x for x in evidence['actual_first_hits'] if x['module'] == module)
            binding = (row['source_sha256'], old['sha256'])
        else:
            raise RuntimeError('unrecognized paid authority '+kind)
        require(binding == (row['source_sha256'], row['object_sha256']), 'paid binding drift '+module)
    return inputs, roots, actual


def validate_report(output, inputs, actual):
    report = read(output/'private-bodies.json')
    expected = {x['module']: x['artifact_sha256'] for x in actual}
    seen = set()
    stages = report['stages']
    require(len(stages) == len(actual), 'incorrect report owner count')
    for row in stages:
        require(row['inherited'] == row['duplicates'] == 0 and not row['base_has_unverified_sources'],
                'replay scope leak '+row['label'])
        for module in row['modules']:
            name = module['module']
            require(name not in seen and sha(module['selected_olean']) == expected[name],
                    'imported body changed '+name)
            seen.add(name)
    private = sum(decl['name'].startswith('_private.') for row in stages for decl in row['declarations'])
    require(seen == set(expected) and report['accepted'] and private == inputs['expected_private_CIs'] and
            sum(row['kernel_calls'] for row in stages) == inputs['expected_kernel_calls'] and
            report['safe_private_original_CIs'] == inputs['expected_new_safe_CIs'] and
            sum(row['raw'] for row in stages) == inputs['expected_raw_CIs'] and
            sum(row['compiler_extras'] for row in stages) == inputs['expected_compiler_extras'] and
            sum(len(row['compiler_runtime']) for row in stages) == 0 and
            len(report['source_body_bindings']) == inputs['source_body_bindings'] and
            len(report['public_mouths']) == inputs['public_mouths'] and
            set(report['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'},
            'incomplete independent audit report')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('repo', 'compiled-root', 'base-lean-path-file', 'output'):
        parser.add_argument('--'+name, type=pathlib.Path, required=True)
    parser.add_argument('--source-root', type=pathlib.Path)
    parser.add_argument('--lean', type=pathlib.Path)
    parser.add_argument('--verify-inputs-only', action='store_true')
    parser.add_argument('--resume-audit', metavar='REPORT_SHA256')
    args = parser.parse_args()
    package = pathlib.Path(__file__).resolve().parent
    inputs, roots, actual = verify_inputs(package, args)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    save(output/'provenance.json', {
        'schema': 'cp514-provenance/v1', 'science': actual,
        'inputs_sha256': sha(package/'inputs.json'), 'old_CI_replays': 0,
        'old_replays': 0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict': 'exact-inputs-verified', 'science': len(actual),
                          'direct_paid_parents': 4, 'pinned_stdlib_imports': 1, 'old_replays': 0}))
        return

    lean = args.lean or pathlib.Path(subprocess.check_output(
        ['elan', 'which', 'lean'], cwd=args.repo/'Lean', text=True).strip())
    env = {**os.environ, 'LEAN_SYSROOT': str(lean.parent.parent),
           'PATH': str(lean.parent)+os.pathsep+os.environ.get('PATH', ''),
           'LEAN_PATH': os.pathsep.join(roots),
           'CP514_CANONICAL_REPORT': str(output/'canonical-application.json'),
           'CP514_CANONICAL_CURRENT': str(output/'canonical-current.json')}
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
        save(cost, {'schema': 'cp514-independent-cost/v1', 'calls': calls, 'actual_calls': len(calls),
                    'known_seconds': sum(x['elapsed_seconds'] for x in calls), 'unknown_calls': 0,
                    'old_compatibility_replays': 0, 'old_certificate_scope_replays': 0,
                    'science_source_recompiles': 0})
        print(json.dumps(row), flush=True)
        if code:
            print(log.read_text()[-7000:], flush=True)
            raise SystemExit(code)

    (output/'certificate.json').unlink(missing_ok=True)
    if args.resume_audit:
        require(sha(output/'private-bodies.json') == args.resume_audit, 'paid audit report changed')
        successes = [x for x in calls if x['exit_code'] == 0 and 'audit' in x['label'] and
                     x['source_sha256'] == sha(package/'Audit.lean') and
                     sha(output/(x['label']+'.log')) == x['log_sha256'] and
                     'PASS new-safe-private=135' in (output/(x['label']+'.log')).read_text()]
        require(len(successes) == 1, 'exact successful audit receipt not unique')
    else:
        require(not calls, 'use a clean output or explicitly resume a paid audit')
        cfg = {'entry': inputs['entry'],
               'stages': [{'label': x['label'], 'modules': [x['module']], 'base': x['base']}
                          for x in inputs['science']],
               'output': str(output/'private-bodies.json'), 'progress': str(output/'ci-progress.jsonl'),
               'current': str(output/'current-ci.json')}
        config = output/'audit-config.json'
        save(config, cfg)
        run('audit', [str(lean), *FLAGS, '--run', str(package/'Audit.lean'), str(config)],
            package/'Audit.lean', config)

    report = validate_report(output, inputs, actual)
    (output/'canonical-application.json').unlink(missing_ok=True)
    run('gate', [str(lean), *FLAGS, '--root='+str(package), '-o', str(output/'Gate.olean'),
                 str(package/'Gate.lean')], package/'Gate.lean')
    application = read(output/'canonical-application.json')
    require(application['accepted'] and application['Meta_calls'] == application['new_proof_premises'] == 0
            and application['kernel_add_decl_calls'] == 1
            and application['conjoined_claims'] == inputs['canonical_claims'],
            'literal same-method application missing or changed')
    verify_inputs(package, args)
    save(output/'certificate.json', {
        'schema': 'cp514-reproduction/v1', 'verdict': 'certified',
        'safe_private_original_CIs': report['safe_private_original_CIs'], 'axioms': report['axioms'],
        'source_level_positive_controls': inputs['typed_source_level_positive_controls'],
        'typed_negative_controls': inputs['typed_negative_controls'],
        'inputs_sha256': sha(package/'inputs.json'), 'raw_body_report_sha256': sha(output/'private-bodies.json'),
        'cost_sha256': sha(cost),
        'canonical_application_sha256': sha(output/'canonical-application.json'),
        'old_compatibility_replays': 0, 'old_certificate_scope_replays': 0,
        'signed_contact_claim': False, 'controller_advance_claim': False})
    print(json.dumps({'verdict': 'certified', 'certificate': str(output/'certificate.json')}), flush=True)


if __name__ == '__main__':
    main()
