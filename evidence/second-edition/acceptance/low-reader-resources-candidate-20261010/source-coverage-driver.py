from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import source_view


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    _, modules, artifacts, _ = source_view.load_map()
    maps = ['docs/second-edition-map.json', 'docs/low-energy-release-map.json']
    result = {'schema': 'h0mework/private-reader-resource-coverage@1',
              'authority_sha256': {p: sha((ROOT / p).read_bytes())
                                   for p in [*maps, 'tools/export-map.json', 'tools/edition_materials.py']},
              'views': [], 'errors': [], 'public_mutation': False}
    for name in maps:
        data = json.loads((ROOT / name).read_bytes())
        for view_id, view in data['runtime_views'].items():
            selected = set(view['paths'])
            supplied = selected | {r['destination'] for r in view.get('resource_bundles', [])}
            resources = {}
            for path in view['paths']:
                if path not in modules:
                    continue
                row = source_view.pick(modules[path], path, None, view['source_commit'])
                if row is None:
                    result['errors'].append({'view': view_id, 'unselected_module': path})
                    continue
                for rewrite in row.get('resource_rewrites', []):
                    original = rewrite['source_artifact']
                    resource = resources.setdefault(original, {'original_path': original, 'importers': [],
                                                             'source_sha256s': set(), 'already_supplied': original in supplied})
                    resource['source_sha256s'].add(rewrite['data_sha256'])
                    resource['importers'].append({'source_path': path, 'source_address': rewrite['source_address']})
            for resource in resources.values():
                original = resource['original_path']
                resource['source_sha256s'] = sorted(resource['source_sha256s'])
                if len(resource['source_sha256s']) != 1:
                    result['errors'].append({'view': view_id, 'conflicting_resource_identity': original})
                candidates = artifacts.get(original, [])
                row = source_view.pick(candidates, original, None, view['source_commit']) if candidates else None
                resource['same_epoch_path_available'] = row is not None
                if row is not None:
                    resource['same_epoch_artifact'] = row['path']
                    resource['same_epoch_source_sha256'] = row['source_sha256']
                    resource['same_epoch_sha_matches_importer'] = row['source_sha256'] in resource['source_sha256s']
                matching = [r for r in candidates if r['source_sha256'] in resource['source_sha256s']]
                resource['matching_public_artifacts'] = sorted({r['path'] for r in matching})
                if not matching:
                    result['errors'].append({'view': view_id, 'unexported_resource_identity': original})
            result['views'].append({'map': name, 'view': view_id, 'source_commit': view['source_commit'],
                                    'resources': list(resources.values()),
                                    'missing_resources': sorted(p for p, r in resources.items() if not r['already_supplied'])})
    result['ok'] = not result['errors']
    output = Path(__file__).parent / 'coverage.json'
    assert not output.exists()
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'ok': result['ok'], 'views': len(result['views']),
                      'affected_views': [{'view': v['view'], 'missing_resources': len(v['missing_resources']),
                                          'missing_epoch_rows': sum(not r['same_epoch_path_available'] for r in v['resources'])}
                                         for v in result['views'] if v['missing_resources']],
                      'errors': result['errors']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
