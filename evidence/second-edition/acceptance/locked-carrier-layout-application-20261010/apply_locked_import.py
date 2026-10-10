from pathlib import Path
import argparse
import copy
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tools'))
import source_view as sv
helper_path = BASE.parent / 'cutoff-time-owner/apply_cutoff_owner.py'
spec = importlib.util.spec_from_file_location('locked_atomic_helpers', helper_path)
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
atomic_bytes, json_like = helpers.atomic_bytes, helpers.json_like


def read(path):
    return json.loads(path.read_bytes())


def main():
    parser = argparse.ArgumentParser(description='Root-owned single exact canonical import for the original Locked carrier')
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    plan_path = BASE / 'plan.json'
    plan = read(plan_path)
    assert sv.sha(plan_path.read_bytes()) == '0462c35987b92177619b1db4b9635c06822cd16496e64f81f59c408ce26585b7'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == plan['head']
    freeze = read(ROOT / '.local/acceptance-execution-20261010/cohort-freeze.json')
    assert freeze['head'] == plan['head'] and freeze['official_dispatch_hold'] is True
    for path, digest in freeze['files'].items():
        if path != 'tools/export-map.json':
            assert sv.sha((ROOT / path).read_bytes()) == digest
    remainder_base = ROOT / '.local/acceptance-execution-20261010/gauge-remainder-owner'
    remainder = read(remainder_base / 'plan.json')
    assert remainder['head'] == plan['head'] and len(remainder['rows']) == 6
    allowed_dirty = {item['path'] for item in remainder['rows']} | {'tools/export-map.json'}
    dirty = subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=ROOT).split(b'\0')
    dirty = [record.decode() for record in dirty if record]
    assert all(record[:2] == ' M' and record[3:] in allowed_dirty for record in dirty)
    assert {record[3:] for record in dirty} == allowed_dirty
    ex_path = ROOT / 'tools/export-map.json'
    before_export_bytes = ex_path.read_bytes()
    exported = read(ex_path)
    before_export = copy.deepcopy(exported)
    rows = {row['path']: row for row in exported['modules']}
    assert len(rows) == len(exported['modules'])
    inverse = {row['target']: row for row in exported['modules']}
    for item in remainder['rows']:
        current = rows[item['path']]
        assert sv.sha((ROOT / item['path']).read_bytes()) == current['target_sha256'] == item['after_target_sha256']
        assert current['private_owner_string_rewrites'] == item['private_owner_string_rewrites']
        assert current['source_sha256'] == item['source_sha256']
        assert sv.sha(sv.module_views(current, inverse)[1]) == item['source_sha256']
    parity_path = ROOT / plan['recursive_parity_path']
    assert sv.sha(parity_path.read_bytes()) == plan['recursive_parity_sha256']
    parity = read(parity_path)
    assert parity['ok'] and len(parity['pairs']) == 20 and len(parity['zero_declaration_layouts']) == 3
    for pair in parity['pairs']:
        assert pair['equal'] and pair['resource_rewrites_equal']
        left, right = pair['retained'], pair['canonical']
        assert rows[left['path']] == left and rows[right['path']] == right
        left_raw, right_raw = (ROOT / left['path']).read_bytes(), (ROOT / right['path']).read_bytes()
        assert sv.sha(left_raw) == left['target_sha256'] and sv.sha(right_raw) == right['target_sha256']
        assert sv.transform(left_raw.decode(), sv.import_tokens(left_raw.decode()),
                            pair['retained_import_map_to_canonical']) == right_raw
    for alias in parity['zero_declaration_layouts']:
        row = inverse[alias['alias']]
        assert (ROOT / row['path']).read_text() == 'import ' + alias['owner'] + '\n'
        assert row['source_sha256'] == alias['source_sha256']
    focused_path = ROOT / plan['focused_verification_path']
    assert sv.sha(focused_path.read_bytes()) == plan['focused_verification_sha256']
    focused = read(focused_path)
    assert focused['ok'] and focused['inputs_unchanged'] and len(focused['steps']) == 3
    assert all(step['exit_code'] == 0 for step in focused['steps'])
    impact_path = ROOT / plan['source_impact']
    assert sv.sha(impact_path.read_bytes()) == plan['source_impact_sha256']
    impact = read(impact_path)
    assert impact['passed32_source_intersections'] == []
    assert impact['old42_modules'] == 25259 and impact['old42_source_intersection'] == []
    assert all(item['candidate_paths'] == [] for item in impact['native_sources'] + impact['charged_sources'])
    assert impact['charged560_completed_true_source_intersection'] == []
    assert impact['live_source_intersection'] == []
    state_path = ROOT / '.local/migration/state2.json'
    before_state_bytes = state_path.read_bytes()
    state = read(state_path)
    before_state = copy.deepcopy(state)
    stored = {}
    for collection in ('files', 'explicit_files'):
        for private in state[collection]:
            assert private['path'] not in stored
            stored[private['path']] = private
    row, private = rows[plan['path']], stored[plan['path']]
    assert row == plan['before_row']
    before = (ROOT / row['path']).read_bytes()
    candidate = (ROOT / plan['candidate_path']).read_bytes()
    assert sv.sha(before) == plan['before_target_sha256'] == private['transformed_sha256']
    assert private['source_sha256'] == row['source_sha256'] and private['target_module'] == row['target']
    prior = sv.module_views(row, inverse)
    before_row, before_private = copy.deepcopy(row), copy.deepcopy(private)
    mapping = {module: (plan['new_import'] if module == plan['old_import'] else module)
               for _, _, module in sv.import_tokens(before.decode())}
    assert sv.transform(before.decode(), sv.import_tokens(before.decode()), mapping) == candidate
    assert sv.sha(candidate) == plan['after_target_sha256']
    row['target_sha256'] = private['transformed_sha256'] = plan['after_target_sha256']
    for record in (row, private):
        assert record['import_map'][plan['old_import']] == plan['original_import_token']
        record['import_map'][plan['new_import']] = record['import_map'].pop(plan['old_import'])
    assert row == plan['candidate_row']
    for new, old in ((row, before_row), (private, before_private)):
        ignored = {'import_map', 'target_sha256', 'transformed_sha256'}
        assert {key: value for key, value in new.items() if key not in ignored} == {key: value for key, value in old.items() if key not in ignored}
    with tempfile.TemporaryDirectory(prefix='locked-inverse-', dir=BASE) as directory:
        shadow = Path(directory)
        path = shadow / row['path']
        path.parent.mkdir(parents=True)
        path.write_bytes(candidate)
        sv.ROOT = shadow
        try:
            assert sv.module_views(row, inverse) == prior
        finally:
            sv.ROOT = ROOT
    assert all(new == old for new, old in zip(exported['modules'], before_export['modules']) if new['path'] != row['path'])
    assert {key: value for key, value in exported.items() if key != 'modules'} == {key: value for key, value in before_export.items() if key != 'modules'}
    for collection in ('files', 'explicit_files'):
        assert all(new == old for new, old in zip(state[collection], before_state[collection]) if new['path'] != row['path'])
    assert {key: value for key, value in state.items() if key not in ('files', 'explicit_files')} == {key: value for key, value in before_state.items() if key not in ('files', 'explicit_files')}
    maps, map_references, map_before = {}, {}, {}
    for name in ('docs/first-release-map.json', 'docs/second-edition-map.json', 'docs/low-energy-release-map.json'):
        path = ROOT / name
        map_before[name] = path.read_bytes()
        data = read(path)
        old, hits = copy.deepcopy(data), []
        def visit(value):
            if isinstance(value, dict):
                public = value.get('public')
                if isinstance(public, dict) and public.get('path') == row['path']:
                    assert public['sha256'] == plan['before_target_sha256']
                    public['sha256'] = plan['after_target_sha256']
                    hits.append(row['path'])
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)
        visit(data)
        map_references[name] = hits
        if hits:
            maps[name] = json_like(path, old, data)
    assert map_references['docs/first-release-map.json'] == []
    first_sha = sv.sha(map_before['docs/first-release-map.json'])
    assert first_sha == '70a109c44e4fa0907f817e5ff7751029562415d82b0a1b48cb854053aeba78be'
    live = subprocess.check_output(['ps', '-axo', 'pid=,command='], text=True)
    assert not any('/bin/lean ' in line and str(ROOT / row['path']) in line for line in live.splitlines())
    assert ex_path.read_bytes() == before_export_bytes and state_path.read_bytes() == before_state_bytes
    assert all((ROOT / name).read_bytes() == raw for name, raw in map_before.items())
    export_bytes = json_like(ex_path, before_export, exported)
    state_bytes = json_like(state_path, before_state, state)
    report = {'schema': 'h0mework/private-locked-import-application@1',
              'ok': True, 'mode': 'apply' if args.apply else 'dry-run',
              'head_before': plan['head'], 'plan_sha256': sv.sha(plan_path.read_bytes()),
              'source_changes': [plan], 'tracked_changed_files': sorted([row['path'], 'tools/export-map.json', *maps]),
              'private_changed_files': ['.local/migration/state2.json'], 'direct_map_references': map_references,
              'existing_remainder6_changes_preserved': True, 'exact_public_and_original_inverse': True,
              'scientific_definitions_proof_bodies_options_namespaces_unchanged': True,
              'all_other_export_state_records_unchanged': True, 'source_epoch_sha_and_origin_unchanged': True,
              'all_retained_and_canonical_complete_source_bodies_preserved': True,
              'registered32_charged560_old42_native_source_intersections': [],
              'formal_kernel_acceptance': False, 'first_release_map_sha256': first_sha}
    if args.apply:
        atomic_bytes(ROOT / row['path'], candidate)
        atomic_bytes(ex_path, export_bytes)
        atomic_bytes(state_path, state_bytes)
        for name, raw in maps.items():
            atomic_bytes(ROOT / name, raw)
        assert sv.module_views(row, inverse) == prior
        assert sv.sha((ROOT / 'docs/first-release-map.json').read_bytes()) == first_sha
    output = BASE / ('applied.json' if args.apply else 'application-dry-run.json')
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'mode': report['mode'], 'ok': True, 'source_files': 1,
                      'tracked_files': len(report['tracked_changed_files']),
                      'direct_map_refs': {name: len(hits) for name, hits in map_references.items()}}))


if __name__ == '__main__':
    main()
