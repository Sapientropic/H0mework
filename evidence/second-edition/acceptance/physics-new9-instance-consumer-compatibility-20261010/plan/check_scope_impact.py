from pathlib import Path
from datetime import datetime, timezone
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import first_release as release
import source_view as sv

ACCEPTANCE = ROOT / '.local/acceptance-execution-20261010'
BASE = ROOT / '.local/physics-acceptance-20261010/new9-local-instance'
plan_path = BASE / 'plan.json'
plan = json.loads(plan_path.read_text())
candidate_paths = {row['path'] for row in plan['rows']}
marker = json.loads((ACCEPTANCE / 'cohort-freeze.json').read_text())
exported = json.loads((ROOT / release.EXPORT_MAP).read_text())
index = release.export_indexes(exported)['modules']
graph, hashes = {}, {}
def header_tokens(text):
    lines = []
    for line in text.splitlines(keepends=True):
        lines.append(line)
        if re.match(r'\s*(?:namespace|open|set_option|noncomputable|section|def|theorem|abbrev|class|structure|variable|example|run_cmd)\b', line):
            try:
                masked = sv.mask_comments_and_strings(''.join(lines)).splitlines()[-1]
            except sv.ViewError:
                continue
            if re.match(r'\s*(?:namespace|open|set_option|noncomputable|section|def|theorem|abbrev|class|structure|variable|example|run_cmd)\b', masked):
                break
    return sv.import_tokens(''.join(lines))
def closure(roots):
    todo, reached, files = list(roots), set(), {}
    while todo:
        module = todo.pop()
        if module in reached or module.split('.')[0] in sv.EXTERNAL:
            continue
        reached.add(module)
        path = release.module_path(module)
        if module not in graph:
            raw = (ROOT / path).read_bytes()
            digest = sv.sha(raw)
            rows = index.get(path, [])
            if rows:
                assert len(rows) == 1 and rows[0]['target'] == module and rows[0]['target_sha256'] == digest, module
            else:
                assert exported.get('paper_aggregators', {}).get(module) == path or exported.get('aggregator') == path, module
            hashes[path] = digest
            graph[module] = [name for _, _, name in header_tokens(raw.decode()) if name.split('.')[0] not in sv.EXTERNAL]
        files[path] = hashes[path]
        todo.extend(graph[module])
    return reached, files
def scope_digest(files):
    return sv.sha(json.dumps(files, sort_keys=True).encode())
def snapshot():
    return {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            'files': {path: sv.sha((ROOT / path).read_bytes()) for path in marker['files']}}
before = snapshot()
assert before['head'] == marker['head']
assert before['files'] == marker['files']
assert all(sv.sha((ROOT / row['path']).read_bytes()) == row['before_public_sha256'] for row in plan['rows'])
package_rows = []
for map_path in ['docs/second-edition-map.json', 'docs/low-energy-release-map.json', 'docs/first-release-map.json']:
    data = json.loads((ROOT / map_path).read_text())
    for package in release.packages(data):
        entries = release.package_entries(data['claims'], package)
        reached, files = closure([package['lean_target']])
        assert all(entry['public']['module'] in reached for _, _, _, entry in entries), package['id']
        verification = package.get('verification', {})
        recorded = verification.get('build')
        registered_digest = recorded.get('source_scope_sha256') if isinstance(recorded, dict) else None
        digest = scope_digest(files)
        package_rows.append({'map': map_path, 'package': package['id'], 'kernel': verification.get('kernel'),
                             'lean_target': package['lean_target'], 'scope_modules': len(files),
                             'source_scope_sha256': digest, 'registered_build_source_scope_sha256': registered_digest,
                             'matches_registered_digest': digest == registered_digest if registered_digest is not None else None,
                             'candidate_intersections': sorted(candidate_paths & set(files))})
        print(json.dumps({'package': package['id'], 'modules': len(files), 'intersections': len(candidate_paths & set(files))}), flush=True)
passed = [row for row in package_rows if row['kernel'] == 'passed']
current_type = next(row for row in package_rows if row['package'] == 'v2-9c73-type-completion')
assert current_type['source_scope_sha256'] == '1db53fa24cb08eed702437b3d63760d608e03d8e9950dbcf265e92b647e48490'
native_rows = []
for owner, name, input_file, scope_file in [
    (ACCEPTANCE, 'runtime-independent-frontier-build-after-repair', 'input-before.json', None),
    (ACCEPTANCE, 'low-nine-owning-proof-frontier-build-c762e780', 'input-before.json', None),
    (BASE.parent, 'r9-gsr-single-native-build-c762e780', 'provenance-before.json', 'source-scope-before.json')]:
    before_path = owner / name / input_file
    actual = json.loads(before_path.read_text())
    files = actual['source_files'] if scope_file is None else json.loads((owner / name / scope_file).read_text())['files']
    result_path = owner / name / 'result.json'
    result = json.loads(result_path.read_text()) if result_path.is_file() else None
    native_rows.append({'run': name, 'input_path': str(before_path.relative_to(ROOT)),
                        'actual_before_head': actual['head'], 'scope_modules': len(files),
                        'source_scope_sha256': scope_digest(files),
                        'candidate_intersections': sorted(candidate_paths & set(files)),
                        'terminal': result is not None,
                        'actual_result': {k: result.get(k) for k in ('ok', 'exit_code', 'inputs_unchanged', 'elapsed_seconds')} if result is not None else None})
charged_before_path = BASE.parent / 'charged-transfer-trust-c762e780-provenance/before.json'
charged = json.loads(charged_before_path.read_text())['package_inputs']['second-edition-physics-charged-transfer']
native_rows.append({'run': 'charged-transfer-trust-c762e780', 'input_path': str(charged_before_path.relative_to(ROOT)),
                    'scope_modules': charged['modules'], 'source_scope_sha256': charged['digest'],
                    'candidate_intersections': sorted(candidate_paths & set(charged['files'])), 'terminal': True})
ci_path = ROOT / '.local/v2-9c73-intake/candidate-ci-plan.json'
ci = json.loads(ci_path.read_text())
protected_parts = {key: value for key, value in ci['parts'].items() if 1 <= value['stage'] <= 7}
assert len(protected_parts) == 42
old42 = []
all_protected_files = {}
for key, part in sorted(protected_parts.items()):
    reached, files = closure(part['modules'])
    all_protected_files.update(files)
    old42.append({'part': key, 'original_placements': len(part['modules']), 'recursive_source_modules': len(files),
                  'source_scope_sha256': scope_digest(files), 'candidate_intersections': sorted(candidate_paths & set(files))})
process_rows = []
process_output = subprocess.check_output(['ps', '-axo', 'pid,ppid,etime,pcpu,rss,command'], text=True).splitlines()
for line in process_output:
    if '/bin/lean ' not in line:
        continue
    parsed = line.strip().split(None, 5)
    if len(parsed) != 6:
        continue
    matches = re.findall(r'./(Lean/H0mework/[^\s]+\.lean)', parsed[5])
    for path in matches:
        process_rows.append({'pid': int(parsed[0]), 'ppid': int(parsed[1]), 'elapsed': parsed[2], 'cpu_percent': parsed[3],
                             'rss_kib': int(parsed[4]), 'source_path': path, 'is_candidate_source': path in candidate_paths})
after = snapshot()
result = {'schema': 'h0mework/private-new9-mixed-spectator-actual-source-scope-impact@1', 'formal_acceptance': False,
          'observed_at': datetime.now(timezone.utc).isoformat(), 'candidate_plan_path': str(plan_path.relative_to(ROOT)),
          'candidate_plan_sha256': sv.sha(plan_path.read_bytes()), 'inputs_unchanged': before == after,
          'input_before': before, 'input_after': after, 'candidate_paths': sorted(candidate_paths),
          'package_intersections': package_rows, 'current_passed_package_count': len(passed),
          'current_passed_intersections': [row for row in passed if row['candidate_intersections']],
          'registered_passed_scope_mismatches': [row for row in passed if row['matches_registered_digest'] is False],
          'current_type_passed_but_not_signed': current_type, 'actual_native_run_intersections': native_rows,
          'protected_ci_plan_path': str(ci_path.relative_to(ROOT)), 'protected_ci_plan_sha256': sv.sha(ci_path.read_bytes()),
          'protected_ci_parts': old42, 'protected_ci_recursive_sources': len(all_protected_files),
          'protected_ci_source_scope_sha256': scope_digest(all_protected_files),
          'protected_ci_candidate_intersections': sorted(candidate_paths & set(all_protected_files)),
          'actual_live_compilers': process_rows,
          'actual_live_candidate_compiler_intersections': [row for row in process_rows if row['is_candidate_source']],
          'scope': 'Actual registered public import closures, selected proof consumption, live source inputs, and 42 original CI part recursive inputs. This is impact evidence, not a kernel acceptance receipt.'}
out = BASE / 'actual-scope-impact.json'
out.write_text(json.dumps(result, indent=2) + '\n')
assert before == after
assert not result['current_passed_intersections']
assert not current_type['candidate_intersections']
assert not result['registered_passed_scope_mismatches']
assert not result['protected_ci_candidate_intersections']
assert not result['actual_live_candidate_compiler_intersections']
assert all(not row['candidate_intersections'] for row in native_rows)
print(json.dumps({k: result[k] for k in ('inputs_unchanged', 'current_passed_package_count', 'current_passed_intersections', 'registered_passed_scope_mismatches', 'protected_ci_recursive_sources', 'protected_ci_candidate_intersections', 'actual_native_run_intersections', 'actual_live_candidate_compiler_intersections')}, indent=2), flush=True)
