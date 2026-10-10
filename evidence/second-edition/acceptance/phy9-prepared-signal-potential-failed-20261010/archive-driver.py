from pathlib import Path
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
RUN = BASE / 'new9-prepared-signal-build-b0374cd0'
PROVENANCE = RUN.with_name(RUN.name + '-provenance')
SNAPSHOT = BASE / 'new4-potential-failure-source-b0374cd0'
NAME = 'phy9-prepared-signal-potential-failed-20261010'
assert not (ROOT / 'evidence/second-edition/acceptance' / NAME).exists()
sys.path.insert(0, str(ROOT / 'tools'))
import source_view

sha = lambda raw: hashlib.sha256(raw).hexdigest()
official = json.loads((RUN / 'result.json').read_bytes())
before = json.loads((PROVENANCE / 'before.json').read_bytes())
after = json.loads((PROVENANCE / 'after.json').read_bytes())
assert not official['ok'] and official['inputs_unchanged'] and before == after
assert sha((RUN / 'result.json').read_bytes()) == 'c77ada2506e80975297ddd80d9f1a0cf94ba47e2be4c2f31b7230d825ca2b626'
exported = json.loads((ROOT / 'tools/export-map.json').read_bytes())
target_path = ('Lean/H0mework/Versions/R9c73a630/ReleaseMaterials/Physics/'
               'LowEnergyPhenomenology/AlphaSource/SourceWholeConfigurationPotential.lean')
row = next(row for row in exported['modules'] if row['path'] == target_path)
inverse = {row['target']: row for row in exported['modules']}
public_source = (ROOT / target_path).read_bytes()
assert sha(public_source) == row['target_sha256']
assert all(packet['files'][target_path] == sha(public_source) for packet in before['package_inputs'].values())
view, original_source = source_view.module_views(row, inverse)
assert sha(original_source) == row['source_sha256']
SNAPSHOT.mkdir()
(SNAPSHOT / 'failed-public-source.lean').write_bytes(public_source)
(SNAPSHOT / 'original-source.lean').write_bytes(original_source)
source_identity = {
    'schema': 'h0mework/private-failed-potential-source-snapshot@1',
    'snapshot_observed_after_run': True, 'exact_build_before_and_after_source_sha256': sha(public_source),
    'source_scope_bytes_unchanged': True, 'target_row': row, 'view_sha256': sha(view),
    'original_source_sha256': sha(original_source), 'original_type_definitions_and_budget_unchanged': True,
    'formal_acceptance': False, 'official_result_sha256': sha((RUN / 'result.json').read_bytes()),
}
(SNAPSHOT / 'source-identity.json').write_text(json.dumps(source_identity, ensure_ascii=False, indent=2) + '\n')
files = {'build.log': RUN / 'build.log', 'result.json': RUN / 'result.json'}
for name in ('argv.json', 'before.json', 'after.json', 'cli.json', 'invocation-source.py', 'plan.json', 'result.json'):
    files['provenance/' + name] = PROVENANCE / name
for name in ('failed-public-source.lean', 'original-source.lean', 'source-identity.json'):
    files['source/' + name] = SNAPSHOT / name
files['archive-driver.py'] = Path(__file__)
helper = ROOT / '.local/second-edition-20261009/archive_acceptance.py'
spec = importlib.util.spec_from_file_location('physics_potential_archive', helper)
archive_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(archive_module)
archive = archive_module.archive(RUN, NAME, expected_ok=False, source_files=files,
                                 text_path_replacements={'runtime/original-source-repository': 'runtime/original-source-repository'})
paths = [row['public_path'] for row in archive['files']]
paths.append('evidence/second-edition/acceptance/' + NAME + '/publication.json')
published = [{'path': path, 'sha256': sha((ROOT / path).read_bytes()),
              'bytes': (ROOT / path).stat().st_size} for path in sorted(paths)]
report = {'schema': 'h0mework/private-potential-failure-public-files@1',
          'archive_name': NAME, 'public_receipt': archive['receipt'],
          'original_result_sha256': sha((RUN / 'result.json').read_bytes()),
          'ok': False, 'inputs_unchanged': True, 'elapsed_seconds': official['results'][0]['elapsed_seconds'],
          'source_snapshot_original_and_failed_public': True,
          'formal_kernel_acceptance': False, 'published_files': published,
          'export_state_maps_registration_or_staging_or_commit_performed': False}
output = BASE / 'new4-potential-failed-published-files-b0374cd0.json'
output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'manifest': output.relative_to(ROOT).as_posix(), 'files': len(published),
                  'manifest_sha256': sha(output.read_bytes()), 'raw_result_sha256': report['original_result_sha256']}))
