from pathlib import Path
import argparse
import copy
import json
import os
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tools'))
import source_view as sv


def read(path):
    return json.loads(path.read_bytes())


def json_like(path, before, after):
    raw = path.read_bytes()
    for indent in (1, 2, 4):
        for sort in (False, True):
            options = {'ensure_ascii': False, 'indent': indent, 'sort_keys': sort}
            if (json.dumps(before, **options) + '\n').encode() == raw:
                return (json.dumps(after, **options) + '\n').encode()
    raise AssertionError('Unknown existing JSON layout: ' + str(path))


def atomic(path, raw):
    mode = stat.S_IMODE(path.stat().st_mode)
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.' + path.name + '.', delete=False) as stream:
        temp = Path(stream.name)
        os.fchmod(stream.fileno(), mode)
        stream.write(raw)
    try:
        os.replace(temp, path)
    finally:
        temp.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description='Root-only existing owner-rule canonical provider alignment')
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    plan_path = BASE / 'plan.json'
    plan = read(plan_path)
    focused = read(BASE / 'environment-verification-62da11e0/result.json')
    assert focused['ok'] and focused['inputs_unchanged'] and len(focused['steps']) == 3
    assert all(step['exit_code'] == 0 for step in focused['steps'])
    impact = read(BASE / 'actual-scope-impact.json')
    assert impact['passed_count'] == 32 and not impact['passed_intersections']
    assert impact['old42_modules'] == 25259 and not impact['old42_intersections']
    assert not impact['native_intersections'][0]['candidate_paths']
    marker = read(BASE.parent / 'cohort-freeze.json')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert head == marker['head'] == '62da11e06ce55da48c1d8e6b8be8bd6047040eae'
    if args.apply:
        assert marker['official_dispatch_hold']
    assert not subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=ROOT)
    assert all(sv.sha((ROOT / path).read_bytes()) == digest for path, digest in marker['files'].items())
    ep, sp = ROOT / 'tools/export-map.json', ROOT / '.local/migration/state2.json'
    exported, state = read(ep), read(sp)
    old_export, old_state = copy.deepcopy(exported), copy.deepcopy(state)
    rows = {row['path']: row for row in exported['modules']}
    inverse = {row['target']: row for row in exported['modules']}
    stored = {row['path']: row for collection in ('files', 'explicit_files') for row in state[collection]}
    changes, views = {}, {}
    with tempfile.TemporaryDirectory(prefix='inverse-shadow-', dir=BASE) as directory:
        shadow = Path(directory)
        for item in plan['rows']:
            row, private = rows[item['path']], stored[item['path']]
            for key in ('path', 'target', 'source_path', 'source_revision', 'source_revisions', 'source_sha256'):
                assert row[key] == item[key]
            before = (ROOT / item['path']).read_bytes()
            assert sv.sha(before) == item['before_target_sha256'] == row['target_sha256'] == private['transformed_sha256']
            old_rules, new_rules = item['previous_private_owner_string_rewrites'], item['private_owner_string_rewrites']
            assert row['private_owner_string_rewrites'] == private['private_owner_string_rewrites'] == old_rules
            previous = sv.module_views(row, inverse)
            candidate = (ROOT / item['candidate_path']).read_bytes()
            assert sv.sha(candidate) == item['after_target_sha256']
            unqualified = sv.rewrite_private_owner_strings(before.decode(), old_rules, reverse=True)
            assert sv.rewrite_private_owner_strings(unqualified, new_rules).encode() == candidate
            assert sv.rewrite_private_owner_strings(candidate.decode(), new_rules, reverse=True) == unqualified
            row['private_owner_string_rewrites'] = copy.deepcopy(new_rules)
            private['private_owner_string_rewrites'] = copy.deepcopy(new_rules)
            row['target_sha256'] = private['transformed_sha256'] = sv.sha(candidate)
            target = shadow / item['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(candidate)
            sv.ROOT = shadow
            try:
                assert sv.module_views(row, inverse) == previous
            finally:
                sv.ROOT = ROOT
            changes[item['path']] = candidate
            views[item['path']] = previous
    paths = set(changes)
    assert len(paths) == 6
    allowed = {'private_owner_string_rewrites', 'target_sha256', 'transformed_sha256'}
    for new, old in zip(exported['modules'], old_export['modules']):
        assert {k: v for k, v in new.items() if new['path'] not in paths or k not in allowed} == {k: v for k, v in old.items() if old['path'] not in paths or k not in allowed}
    for collection in ('files', 'explicit_files'):
        for new, old in zip(state[collection], old_state[collection]):
            assert {k: v for k, v in new.items() if new['path'] not in paths or k not in allowed} == {k: v for k, v in old.items() if old['path'] not in paths or k not in allowed}
    assert {k: v for k, v in exported.items() if k != 'modules'} == {k: v for k, v in old_export.items() if k != 'modules'}
    assert {k: v for k, v in state.items() if k not in ('files', 'explicit_files')} == {k: v for k, v in old_state.items() if k not in ('files', 'explicit_files')}
    maps, refs = {}, {}
    for name in ('docs/first-release-map.json', 'docs/second-edition-map.json', 'docs/low-energy-release-map.json'):
        current = read(ROOT / name)
        previous = copy.deepcopy(current)
        hits = []

        def visit(value):
            if isinstance(value, dict):
                public = value.get('public')
                if isinstance(public, dict) and public.get('path') in paths:
                    path = public['path']
                    expected = next(item['before_target_sha256'] for item in plan['rows'] if item['path'] == path)
                    assert public['sha256'] == expected
                    public['sha256'] = rows[path]['target_sha256']
                    hits.append(path)
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)

        visit(current)
        refs[name] = hits
        if hits:
            maps[name] = json_like(ROOT / name, previous, current)
    assert not refs['docs/first-release-map.json']
    first_sha = sv.sha((ROOT / 'docs/first-release-map.json').read_bytes())
    assert first_sha == '70a109c44e4fa0907f817e5ff7751029562415d82b0a1b48cb854053aeba78be'
    processes = subprocess.check_output(['ps', '-axo', 'pid=,command='], text=True)
    for path in paths:
        assert not any('/bin/lean ' in line and str(ROOT / path) in line for line in processes.splitlines())
    report = {'schema': 'h0mework/exact-gauge-remainder-canonical-owner-application@1',
              'mode': 'apply' if args.apply else 'dry-run', 'ok': True, 'head_before': head,
              'plan_sha256': sv.sha(plan_path.read_bytes()), 'source_changes': plan['rows'],
              'tracked_changed_files': sorted([*paths, 'tools/export-map.json', *maps]),
              'private_changed_files': ['.local/migration/state2.json'], 'direct_map_references': refs,
              'exact_original_and_public_view_inverse': True, 'math_imports_options_unchanged': True,
              'tool_change': False, 'budget_change': False, 'formal_acceptance': False,
              'first_release_map_sha256': first_sha, 'live_source_intersections': []}
    if args.apply:
        for path, raw in changes.items():
            atomic(ROOT / path, raw)
        atomic(ep, json_like(ep, old_export, exported))
        atomic(sp, json_like(sp, old_state, state))
        for path, raw in maps.items():
            atomic(ROOT / path, raw)
        for path in paths:
            assert sv.module_views(rows[path], inverse) == views[path]
    (BASE / ('applied.json' if args.apply else 'application-dry-run.json')).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'mode': report['mode'], 'ok': True, 'sources': 6, 'tracked_files': len(report['tracked_changed_files']),
                      'map_refs': {name: len(hits) for name, hits in refs.items()}}), flush=True)


if __name__ == '__main__':
    main()
