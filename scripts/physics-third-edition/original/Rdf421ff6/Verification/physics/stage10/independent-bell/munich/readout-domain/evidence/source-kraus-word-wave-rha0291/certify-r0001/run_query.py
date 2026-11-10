#!/usr/bin/env python3
"""Inspect the frozen complete all-word L2 wave and Born measure producer without recompiling a PASS."""

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path('runtime/Documents/Homework')


def record(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


def verify(expected):
    actual = record(expected['path'])
    assert actual['sha256'] == expected['sha256'] and actual['bytes'] == expected['bytes']


def frozen(commit, path):
    path = Path(path)
    relative = path.resolve().relative_to(ROOT).as_posix()
    assert subprocess.check_output(['git', '--no-optional-locks', 'show',
        f'{commit}:{relative}'], cwd=ROOT) == path.read_bytes()


def write_json(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def verify_lookup(plan, roots):
    # Lean SearchPath.findWithExt selects a package root before its full module.
    resolved = []
    for expected in plan['qualified_module_lookup']:
        parts = expected['module'].split('.')
        selected = next((root for root in roots if (root / parts[0]).is_dir()
            or (root / (parts[0] + '.olean')).exists()), None)
        assert selected is not None, expected['module']
        actual = selected.joinpath(*parts).with_suffix('.olean')
        assert actual.resolve() == Path(expected['artifact']['path']).resolve(), str(actual)
        verify(expected['artifact'])
        resolved.append({'module': expected['module'], 'selected_root': str(selected),
            'artifact': record(actual)})
    return resolved


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--query-commit', required=True)
    args = parser.parse_args()
    assert len(args.query_commit) == 40 and all(c in '0123456789abcdef' for c in args.query_commit)
    group = Path(__file__).resolve().parent
    frozen(args.query_commit, group / 'source-stopped.json')
    stopped = json.loads((group / 'source-stopped.json').read_text())
    for name, expected in stopped['candidate_files'].items():
        verify({**expected, 'path': str(group / name)})
        frozen(args.query_commit, group / name)
    plan = json.loads((group / 'query-plan.json').read_text())
    assert str(group) == plan['formal_directory']
    for item in plan['verify_before_query']:
        verify(item)
    for item in plan['fixed_sources']:
        verify(item['source'])
        frozen(item['commit'], item['source']['path'])
    qualified = plan['qualified_candidate']
    paid = json.loads(Path(qualified['kernel_return']['path']).read_text())
    natural = json.loads(Path(qualified['natural_return']['path']).read_text())
    closed = json.loads(Path(qualified['completion']['path']).read_text())
    assert paid['module'] == 'SourceKrausWordWave291'
    assert paid['source'] == qualified['source'] and paid['artifact'] == qualified['artifact']
    assert paid['source_commit'] == qualified['source_commit']
    assert paid['host_commit'] == natural['host_commit'] == closed['host_commit'] == qualified['host_commit']
    assert paid['natural_exit_code'] == paid['exit'] == 0 and paid['accepted']
    assert paid['trust'] == 0 and paid['warningAsError'] and not paid['cached']
    assert paid['true_child_wait_completed'] and paid['timeout_seconds'] is None
    assert paid['dependencies_unchanged'] and paid['source_and_parent_guards']
    assert paid['qualification_error'] is None and paid['observer_metadata_error'] is None
    assert paid['qualified_dependency_recompiles'] == paid['old_PASS_replays'] == 0
    assert paid['complete_log'] == qualified['complete_log'] and qualified['complete_log']['bytes'] == 0
    assert paid['dependencies'] == plan['qualified_candidate_dependencies']
    assert paid['actual_module_lookup_before'] == paid['actual_module_lookup_after']
    assert natural['natural_exit_code'] == 0 and natural['true_child_wait_completed']
    assert natural['source'] == qualified['source'] and natural['complete_log'] == qualified['complete_log']
    assert natural['observer_metadata_error'] is None and natural['timeout_seconds'] is None
    assert closed['exit'] == 0 and closed['completed_modules'] == [paid]
    assert closed['unexecuted_modules'] == []
    for context in plan['lake_context']:
        verify(context)
    helper_spec = importlib.util.spec_from_file_location('cached_lean_word_wave291_query_metadata', plan['helper']['path'])
    helper = importlib.util.module_from_spec(helper_spec)
    helper_spec.loader.exec_module(helper)
    environment = os.environ.copy()
    environment.pop('LEAN_PATH', None)
    roots = [Path(value) for value in plan['qualified_roots_first']]
    for path in helper.lean_library_roots(ROOT / 'Lean', environment):
        if path not in roots:
            roots.append(path)
    lookup_before = verify_lookup(plan, roots)
    query = group / plan['query_module_file']
    query_before = record(query)
    dependencies = helper.dependency_fingerprint(query, roots)
    assert dependencies == plan['expected_query_dependencies']
    compiler = helper.compiler_githash(ROOT / 'Lean', environment)
    assert compiler == plan['compiler_githash']
    output = Path(plan['output_directory'])
    output.mkdir(parents=True, exist_ok=False)
    artifact = output / 'compiled/SourceKrausWordWave291CertifyQuery.olean'
    artifact.parent.mkdir(parents=True)
    command = ['lake', 'env', '/usr/bin/env', 'LEAN_PATH=' + os.pathsep.join(map(str, roots)),
        'lean', '--trust=0', '-R', str(group), '-j1', '-M16000',
        '-DwarningAsError=true', '-DmaxErrors=80', '-DElab.async=false',
        '-o', str(artifact), str(query)]
    write_json(output / 'start.json', {'query_commit': args.query_commit, 'command': command,
        'query': query_before, 'candidate': qualified, 'dependencies': dependencies,
        'actual_module_lookup': lookup_before, 'ordered_roots': list(map(str, roots)),
        'started_at_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'timeout_seconds': None, 'automatic_restarts': 0, 'candidate_recompiles': 0,
        'qualified_dependency_recompiles': 0, 'controller_advance': False})
    began = time.monotonic()
    metadata_error = None
    log = output / 'query.log'
    with log.open('x') as stream:
        child = subprocess.Popen(command, cwd=ROOT / 'Lean', env=environment,
            stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            write_json(output / 'child.json', {'pid': child.pid, 'observer_pid': os.getpid()})
        except Exception as error:
            metadata_error = {'type': type(error).__name__, 'message': str(error)}
        finally:
            natural_exit = child.wait()
    # Persist the paid child exit before any qualification guard can fail.
    natural_path = output / 'natural-return.json'
    write_json(natural_path, {'schema': 'source-kraus-word-wave291/query-natural-return/r0001',
        'query_commit': args.query_commit, 'candidate_source_commit': qualified['source_commit'],
        'query': query_before, 'candidate': qualified, 'command': command,
        'pid': child.pid, 'observer_pid': os.getpid(), 'natural_exit_code': natural_exit,
        'true_child_wait_completed': True, 'complete_log': record(log),
        'seconds_to_natural_return': round(time.monotonic() - began, 3),
        'observer_metadata_error_before_wait': metadata_error, 'qualification_status': 'pending',
        'timeout_seconds': None, 'automatic_restarts': 0, 'candidate_recompiles': 0,
        'qualified_dependency_recompiles': 0, 'controller_advance': False,
        'returned_at_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat()})
    lookup_after = None
    after = None
    query_after = None
    guards = False
    qualification_error = None
    qualification_stage = 'module_lookup'
    try:
        lookup_after = verify_lookup(plan, roots)
        qualification_stage = 'qualified_artifacts'
        for item in plan['qualified_artifacts']:
            verify(item)
        qualification_stage = 'fixed_sources'
        for item in plan['fixed_sources']:
            verify(item['source'])
        qualification_stage = 'preserved_evidence'
        for item in plan['verify_before_query']:
            verify(item)
        qualification_stage = 'query_and_dependency_fingerprint'
        after = helper.dependency_fingerprint(query, roots)
        query_after = record(query)
        guards = after == dependencies and query_after == query_before and lookup_before == lookup_after
    except Exception as error:
        qualification_error = {'stage': qualification_stage,
            'type': type(error).__name__, 'message': str(error)}
    success = (natural_exit == 0 and guards and artifact.is_file()
        and metadata_error is None and qualification_error is None)
    returned = {'module': 'SourceKrausWordWave291CertifyQuery', 'query_commit': args.query_commit,
        'query': query_before, 'query_after': query_after, 'candidate': qualified, 'command': command,
        'natural_return': record(natural_path), 'qualification_error': qualification_error,
        'artifact': record(artifact) if artifact.is_file() else None,
        'natural_exit_code': natural_exit, 'exit': 0 if success else natural_exit or 1,
        'trust': 0, 'werror': True, 'cached': False, 'compiler_githash': compiler,
        'seconds': round(time.monotonic() - began, 3), 'complete_log': record(log),
        'dependencies': dependencies, 'dependencies_unchanged': after == dependencies,
        'query_unchanged': query_after == query_before,
        'actual_module_lookup_before': lookup_before, 'actual_module_lookup_after': lookup_after,
        'qualified_sources_and_artifacts_unchanged': guards,
        'true_child_wait_completed': True, 'observer_metadata_error': metadata_error,
        'timeout_seconds': None, 'automatic_restarts': 0, 'candidate_recompiles': 0,
        'qualified_dependency_recompiles': 0, 'controller_advance': False}
    write_json(output / 'query-return.json', returned)
    write_json(output / 'completion.json', {'query_commit': args.query_commit,
        'return': record(output / 'query-return.json'), 'complete_log': record(log),
        'natural_return': record(natural_path), 'qualification_error': qualification_error,
        'natural_exit_code': natural_exit, 'driver_exit_code': returned['exit'],
        'true_child_wait_completed': True, 'observer_metadata_error': metadata_error,
        'candidate_recompiles': 0, 'qualified_dependency_recompiles': 0, 'automatic_restarts': 0,
        'completed_at_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat()})
    print(json.dumps(returned, ensure_ascii=False, indent=2))
    return returned['exit']


if __name__ == '__main__':
    raise SystemExit(main())
