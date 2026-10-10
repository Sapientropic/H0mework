from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tools'))
import edition_materials
import source_view


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def inputs():
    return {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            'sha256': {p: sha((ROOT / p).read_bytes()) for p in
                       ['docs/second-edition-map.json', 'docs/low-energy-release-map.json',
                        'tools/export-map.json', 'tools/edition_materials.py', 'tools/source_view.py']}}


def verify(view_id, output, requirement):
    identity = json.loads((output / 'view-identity.json').read_bytes())
    files = {p: sha((output / p).read_bytes()) == digest
             for p, digest in identity['source_files'].items()}
    resources = []
    for resource in requirement['resources']:
        for importer in resource['importers']:
            source = output / importer['source_path']
            target = (source.parent / importer['source_address']).resolve()
            expected = output / resource['original_path']
            address_present = importer['source_address'] in source.read_text()
            resolves = target == expected and target.is_file()
            digest_matches = resolves and sha(target.read_bytes()) == identity['source_files'].get(resource['original_path'])
            resources.append({**importer, 'original_resource_path': resource['original_path'],
                              'address_present': address_present, 'resolves': resolves,
                              'digest_matches': digest_matches,
                              'ok': address_present and resolves and digest_matches})
    return {'view': view_id, 'view_path': output.relative_to(ROOT).as_posix(),
            'identity_receipt': (output / 'view-identity.json').relative_to(ROOT).as_posix(),
            'identity_receipt_sha256': sha((output / 'view-identity.json').read_bytes()),
            'source_files_checked': len(files), 'file_identity_ok': all(files.values()),
            'resources_checked': len(requirement['resources']), 'resource_addresses': resources,
            'complete_resource_addresses': all(r['ok'] for r in resources),
            'ok': all(files.values()) and all(r['ok'] for r in resources)}


def main():
    before = inputs()
    coverage = json.loads((BASE / 'coverage.json').read_bytes())
    affected = [v for v in coverage['views'] if v['map'] == 'docs/low-energy-release-map.json' and v['missing_resources']]
    output_base = BASE / 'actual-views'
    assert not output_base.exists()
    output_base.mkdir()
    result = {'schema': 'h0mework/private-reader-resource-candidate-execution@1',
              'started_at': datetime.now(timezone.utc).isoformat(), 'input_before': before,
              'candidate_map_sha256': sha((BASE / 'low-energy-map-candidate.json').read_bytes()),
              'original_negative': None, 'candidate_positive': [], 'scientific_recalculation': False,
              'Lean_recompiled': False, 'public_mutation': False, 'command': sys.argv}
    baseline = next(v for v in affected if v['view'] == 'low-energy-l26-action-clock-71e')
    begin = time.monotonic()
    original_output = output_base / (baseline['view'] + '-original')
    original = edition_materials.restore('low-energy', baseline['view'], original_output)
    check = verify(baseline['view'], original_output, baseline)
    assert original['status'] == 'verified' and check['file_identity_ok']
    assert not check['complete_resource_addresses']
    check['elapsed_seconds'] = round(time.monotonic() - begin, 3)
    check['existing_engine_status'] = original['status']
    check['expected_incomplete'] = True
    result['original_negative'] = check
    print(json.dumps({'view': baseline['view'], 'scope': 'original metadata',
                      'missing_resource_addresses': sum(not r['ok'] for r in check['resource_addresses']),
                      'elapsed_seconds': check['elapsed_seconds']}, ensure_ascii=False), flush=True)
    original_edition = edition_materials.EDITIONS['low-energy']
    edition_materials.EDITIONS['low-energy'] = ((BASE / 'low-energy-map-candidate.json').relative_to(ROOT).as_posix(), original_edition[1])
    try:
        for requirement in affected:
            assert inputs() == before
            begin = time.monotonic()
            output = output_base / (requirement['view'] + '-candidate')
            restored = edition_materials.restore('low-energy', requirement['view'], output)
            check = verify(requirement['view'], output, requirement)
            assert restored['status'] == 'verified' and check['ok']
            check['elapsed_seconds'] = round(time.monotonic() - begin, 3)
            result['candidate_positive'].append(check)
            print(json.dumps({'view': requirement['view'], 'ok': check['ok'],
                              'resources': check['resources_checked'], 'source_files': check['source_files_checked'],
                              'elapsed_seconds': check['elapsed_seconds']}, ensure_ascii=False), flush=True)
            (BASE / 'candidate-execution-progress.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    finally:
        edition_materials.EDITIONS['low-energy'] = original_edition
    result['input_after'] = inputs()
    result['inputs_unchanged'] = before == result['input_after']
    result['finished_at'] = datetime.now(timezone.utc).isoformat()
    result['ok'] = result['inputs_unchanged'] and len(result['candidate_positive']) == len(affected)
    (BASE / 'result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'ok': result['ok'], 'inputs_unchanged': result['inputs_unchanged'],
                      'candidate_views': len(result['candidate_positive'])}, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
