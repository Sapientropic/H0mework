from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
HELPER = ROOT / '.local/second-edition-20261009/archive_acceptance.py'
source = HELPER.read_text()
old = "'packages':doc.get('identity_scope',{}).get('packages',[]),"
new = "'packages':(doc.get('identity_scope') if isinstance(doc.get('identity_scope'),dict) else {}).get('packages',[]),"
assert source.count(old) == 1
namespace = {'__file__': str(HELPER), '__name__': 'cutoff_archive_acceptance'}
exec(compile(source.replace(old, new), str(HELPER), 'exec'), namespace)

handoff = json.loads((BASE / 'archive-handoff.json').read_bytes())
names = [
    'cutoff-time-owner-first-fixture-failed-20261010',
    'cutoff-time-owner-consumer-20261010',
    'cutoff-time-owner-application-20261010',
]
assert not (ROOT / 'evidence/second-edition/acceptance' / names[2]).exists()
replacements = {'runtime/original-source-repository': 'runtime/original-source-repository'}
archives = []
for item, name in zip(handoff['items'], names[:2]):
    files = {row['archive_relative']: ROOT / row['source'] for row in item['required_files']}
    previous = ROOT / 'evidence/second-edition/acceptance' / name / 'publication.json'
    if previous.exists():
        sealed = json.loads(previous.read_bytes())
        assert sealed['status'] == ('passed' if item['ok'] else 'failed')
        expected = {row['source']: row['sha256'] for row in item['required_files']}
        assert {row['original_runtime_path']: row['source_sha256'] for row in sealed['files']} == expected
        assert all(hashlib.sha256((ROOT / row['public_path']).read_bytes()).hexdigest() == row['target_sha256']
                   for row in sealed['files'])
        archives.append(sealed)
    else:
        archives.append(namespace['archive'](ROOT / item['source_directory'], name,
                                            expected_ok=item['ok'], source_files=files,
                                            text_path_replacements=replacements))
application = {row['archive_relative']: ROOT / row['source']
               for row in handoff['adapter_required_files']}
application['result.json'] = BASE / 'applied.json'
application['archive-handoff.json'] = BASE / 'archive-handoff.json'
application['archive-driver.py'] = Path(__file__)
archives.append(namespace['archive'](BASE, names[2], expected_ok=True,
                                    source_files=application, text_path_replacements=replacements))
published = []
for name, archive in zip(names, archives):
    paths = [row['public_path'] for row in archive['files']]
    paths.append('evidence/second-edition/acceptance/' + name + '/publication.json')
    for relative in paths:
        path = ROOT / relative
        published.append({'path': relative, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                          'bytes': path.stat().st_size})
report = {'schema': 'h0mework/private-cutoff-public-archive-files@1',
          'archives': [{'name': name, 'status': record['status'],
                        'receipt': record['receipt'], 'files': len(record['files']) + 1}
                       for name, record in zip(names, archives)],
          'published_files': published, 'export_state_or_maps_registration_performed': False,
          'staging_commit_signing_performed': False,
          'archive_helper_source_sha256': hashlib.sha256(HELPER.read_bytes()).hexdigest(),
          'helper_private_adaptation': {'old': old, 'new': new,
                                        'reason': 'The original identity_scope string remains intact; it does not declare a package list.'}}
output = BASE / 'published-files.json'
output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'manifest': output.relative_to(ROOT).as_posix(), 'files': len(published),
                  'archives': report['archives']}))
