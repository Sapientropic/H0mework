from pathlib import Path
import argparse
import copy
import importlib.util
import json
import os
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tools'))
spec = importlib.util.spec_from_file_location('cutoff_source_view', ROOT / 'tools/source_view.py')
sv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sv)
sv.ROOT = ROOT


def read(path):
    return json.loads(path.read_bytes())


def atomic_bytes(path, data):
    mode = stat.S_IMODE(path.stat().st_mode)
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.' + path.name + '.', delete=False) as stream:
        temporary = Path(stream.name)
        os.fchmod(stream.fileno(), mode)
        stream.write(data)
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def json_like(path, before, after):
    raw = path.read_bytes()
    for indent in (1, 2, 4):
        for sorted_keys in (False, True):
            options = dict(ensure_ascii=False, indent=indent, sort_keys=sorted_keys)
            if (json.dumps(before, **options) + '\n').encode() == raw:
                return (json.dumps(after, **options) + '\n').encode()
    raise AssertionError('Unrecognized existing JSON format: ' + str(path))


def current_dirty_paths():
    raw = subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=ROOT)
    records = [part.decode() for part in raw.split(b'\0') if part]
    assert all(record[:2] in (' M', '??') for record in records), 'Root window must not contain staged/renamed files'
    return {record[3:] for record in records}


def main():
    parser = argparse.ArgumentParser(description='Root-owned one-source CutoffTime private Name-owner adaptation')
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    plan_path = BASE / 'plan.json'
    plan = read(plan_path)
    assert sv.sha(plan_path.read_bytes()) == 'c0a1e9fae6a6a2b491ec79c607102b1dcc562c0ba7aa2066771fc970c48653f3'
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert head == plan['head_at_observation']
    marker = read(ROOT / '.local/acceptance-execution-20261010/cohort-freeze.json')
    assert marker['head'] == head and marker['official_dispatch_hold'] is True

    tuple_base = BASE.parent / 'joint-price-owner'
    tuple_plan = read(tuple_base / 'plan.json')
    tuple_applied = read(tuple_base / 'applied.json')
    assert tuple_applied['ok'] and tuple_applied['mode'] == 'apply'
    assert sv.sha((tuple_base / 'plan.json').read_bytes()) == tuple_applied['plan_sha256']
    assert sv.sha((ROOT / 'tools/source_view.py').read_bytes()) == tuple_plan['tool_candidate_sha256']
    assert sv.sha((ROOT / 'tools/test_publication.py').read_bytes()) == tuple_plan['test_candidate_sha256']
    dirty_before = current_dirty_paths()
    known_root_files = set(tuple_applied['tracked_changed_files']) | {
        'docs/proof-build-adaptations.md', 'docs/second-edition-map.json',
        'docs/low-energy-release-map.json',
    }
    def root_owned(path):
        return path in known_root_files or path.startswith('evidence/second-edition/acceptance/')
    assert all(root_owned(path) for path in dirty_before), 'Unexpected dirty path outside the existing Root window'

    impact_path = ROOT / plan['source_impact']
    impact = read(impact_path)
    assert sv.sha(impact_path.read_bytes()) == plan['source_impact_sha256']
    assert impact['passed_package_intersections'] == []
    assert impact['old42_sources'] == 25259 and impact['old42_intersection'] == []
    assert all(row['candidate_paths'] == [] for row in impact['native_source_intersections'])
    assert impact['live_compiler_source_intersections'] == []
    assert [(row['map'], row['package']) for row in impact['affected_packages']] == [
        ('docs/second-edition-map.json', 'v2-9c73-charged-transfer')]
    focused_path = ROOT / plan['actual_payer_owner_verification']
    focused = read(focused_path)
    assert sv.sha(focused_path.read_bytes()) == plan['original_fixture_false_result_sha256']
    assert not focused['ok'] and focused['inputs_unchanged']
    assert focused['steps'][:2] == plan['actual_payer_and_full_module_steps']
    assert all(step['exit_code'] == 0 for step in focused['steps'][:2])
    consumer_path = ROOT / plan['independent_consumer_result']
    consumer = read(consumer_path)
    assert sv.sha(consumer_path.read_bytes()) == plan['independent_consumer_result_sha256']
    assert consumer['ok'] and consumer['inputs_unchanged'] and consumer['exit_code'] == 0

    ex_path = ROOT / 'tools/export-map.json'
    export_before_bytes = ex_path.read_bytes()
    exported = read(ex_path)
    before_export = copy.deepcopy(exported)
    rows = {row['path']: row for row in exported['modules']}
    assert len(rows) == len(exported['modules'])
    inverse = {row['target']: row for row in exported['modules']}
    for item in tuple_plan['rows']:
        assert sv.sha((ROOT / item['path']).read_bytes()) == item['after_target_sha256']
        assert rows[item['path']]['target_sha256'] == item['after_target_sha256']
        assert rows[item['path']]['private_owner_string_rewrites'] == item['private_owner_string_rewrites']
    for name, original in plan['actual_original_provider_rows'].items():
        assert rows[original['path']] == original, name
        assert sv.sha((ROOT / original['path']).read_bytes()) == original['target_sha256']
    state_path = ROOT / '.local/migration/state2.json'
    state_before_bytes = state_path.read_bytes()
    state = read(state_path)
    before_state = copy.deepcopy(state)
    stored = {}
    for collection in ('files', 'explicit_files'):
        for private in state[collection]:
            assert private['path'] not in stored
            stored[private['path']] = private
    row = rows[plan['path']]
    private = stored[plan['path']]
    for key in ('path', 'target', 'source_path', 'source_revision', 'source_revisions', 'source_sha256'):
        assert row[key] == plan[key]
    assert row.get('source_origin') == plan['source_origin']
    assert private['source_sha256'] == row['source_sha256'] and private['target_module'] == row['target']
    before = (ROOT / row['path']).read_bytes()
    assert sv.sha(before) == row['target_sha256'] == private['transformed_sha256'] == plan['before_target_sha256']
    assert not row.get('private_owner_expression_rewrites') and not private.get('private_owner_expression_rewrites')
    prior_views = sv.module_views(row, inverse)
    candidate = (ROOT / plan['candidate_path']).read_bytes()
    assert sv.sha(candidate) == plan['after_target_sha256']
    rules = plan['private_owner_expression_rewrites']
    assert len(rules) == 3 and all(rule['count'] == 1 for rule in rules)
    assert sv.rewrite_private_owner_expressions(before.decode(), rules).encode() == candidate
    assert sv.rewrite_private_owner_expressions(candidate.decode(), rules, reverse=True).encode() == before
    old_row, old_private = copy.deepcopy(row), copy.deepcopy(private)
    row['private_owner_expression_rewrites'] = copy.deepcopy(rules)
    private['private_owner_expression_rewrites'] = copy.deepcopy(rules)
    row['target_sha256'] = private['transformed_sha256'] = sv.sha(candidate)
    for new, old in ((row, old_row), (private, old_private)):
        permitted = {'private_owner_expression_rewrites', 'target_sha256', 'transformed_sha256'}
        assert {k: v for k, v in new.items() if k not in permitted} == {k: v for k, v in old.items() if k not in permitted}
    with tempfile.TemporaryDirectory(prefix='cutoff-inverse-', dir=BASE) as directory:
        shadow = Path(directory)
        shadow_path = shadow / row['path']
        shadow_path.parent.mkdir(parents=True, exist_ok=True)
        shadow_path.write_bytes(candidate)
        sv.ROOT = shadow
        try:
            assert sv.module_views(row, inverse) == prior_views
        finally:
            sv.ROOT = ROOT
    assert all(new == old for new, old in zip(exported['modules'], before_export['modules']) if new['path'] != row['path'])
    assert {k: v for k, v in exported.items() if k != 'modules'} == {k: v for k, v in before_export.items() if k != 'modules'}
    assert {k: v for k, v in state.items() if k not in ('files', 'explicit_files')} == {k: v for k, v in before_state.items() if k not in ('files', 'explicit_files')}
    for collection in ('files', 'explicit_files'):
        assert all(new == old for new, old in zip(state[collection], before_state[collection]) if new['path'] != row['path'])

    map_changes, references, map_before_bytes = {}, {}, {}
    for name in ('docs/first-release-map.json', 'docs/second-edition-map.json', 'docs/low-energy-release-map.json'):
        map_before_bytes[name] = (ROOT / name).read_bytes()
        data = read(ROOT / name)
        old_map, hits = copy.deepcopy(data), []
        def visit(value):
            if isinstance(value, dict):
                public = value.get('public')
                if isinstance(public, dict) and public.get('path') == row['path']:
                    assert public['sha256'] == plan['before_target_sha256']
                    public['sha256'] = row['target_sha256']
                    hits.append(row['path'])
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)
        visit(data)
        references[name] = hits
        if hits:
            map_changes[name] = json_like(ROOT / name, old_map, data)
    assert references['docs/first-release-map.json'] == []
    first_sha = sv.sha(map_before_bytes['docs/first-release-map.json'])
    assert first_sha == '70a109c44e4fa0907f817e5ff7751029562415d82b0a1b48cb854053aeba78be'
    live = subprocess.check_output(['ps', '-axo', 'pid=,command='], text=True)
    assert not any('/bin/lean ' in line and str(ROOT / row['path']) in line for line in live.splitlines())
    assert current_dirty_paths() == dirty_before
    assert ex_path.read_bytes() == export_before_bytes and state_path.read_bytes() == state_before_bytes
    assert all((ROOT / name).read_bytes() == raw for name, raw in map_before_bytes.items())
    export_bytes = json_like(ex_path, before_export, exported)
    state_bytes = json_like(state_path, before_state, state)
    report = {
        'schema': 'h0mework/private-cutoff-time-owner-application@1',
        'mode': 'apply' if args.apply else 'dry-run', 'ok': True,
        'head_before': head, 'existing_root_dirty_paths': sorted(dirty_before),
        'plan_sha256': sv.sha(plan_path.read_bytes()), 'source_changes': [plan],
        'tracked_changed_files': sorted([row['path'], 'tools/export-map.json', *map_changes]),
        'private_changed_files': ['.local/migration/state2.json'],
        'direct_map_references': references, 'exact_public_and_original_inverse': True,
        'source_origin_epoch_and_original_sha256_unchanged': True,
        'imports_options_definitions_types_and_math_unchanged': True,
        'six_tuple_inputs_and_all_other_export_state_records_unchanged': True,
        'registered32_and_old42_and_runtime_and_low_source_intersections': [],
        'live_source_intersections': [], 'formal_kernel_acceptance': False,
        'affected_package': 'v2-9c73-charged-transfer',
        'existing_source_view_api_only': True, 'first_release_map_sha256': first_sha,
        'export_map_before_sha256': sv.sha(export_before_bytes),
        'export_map_after_sha256': sv.sha(export_bytes),
    }
    if args.apply:
        atomic_bytes(ROOT / row['path'], candidate)
        atomic_bytes(ex_path, export_bytes)
        atomic_bytes(state_path, state_bytes)
        for name, raw in map_changes.items():
            atomic_bytes(ROOT / name, raw)
        assert sv.module_views(row, inverse) == prior_views
        assert sv.sha((ROOT / 'docs/first-release-map.json').read_bytes()) == first_sha
    output = BASE / ('applied.json' if args.apply else 'application-dry-run.json')
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'mode': report['mode'], 'ok': True, 'source_files': 1, 'rules': 3,
                      'tracked_files': len(report['tracked_changed_files']),
                      'direct_map_refs': {key: len(value) for key, value in references.items()}}))


if __name__ == '__main__':
    main()
