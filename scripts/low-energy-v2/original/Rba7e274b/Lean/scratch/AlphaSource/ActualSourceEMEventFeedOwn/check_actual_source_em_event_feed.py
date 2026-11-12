"""Bind per-leaf kernel evidence and enforce the exact published claim scope."""
import argparse
import hashlib
import json
from pathlib import Path

OWN = Path(__file__).resolve().parent
ROOT = OWN.parents[3]
AUDIT = Path((OWN / 'audit-dir.txt').read_text().strip())
PROD = ROOT / 'Verification/physics/low-energy-phenomenology/alpha-source/em-identification'
N = 'LowEnergy.GaussComposite.ActualSourceEMEventFeed.'
CLAIM = {'connected_source_background_retained': True,
         'static_ir_cut_invariance': True, 'physical_n3_window_cut_invariance': True,
         'native_speed_equals_correctedEMc': False,
         'finite_photon_full_cut_invariance': False,
         'source_laws_select_unique_observation_tuple': False}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(source_feed=None, source_cut=None, scope_override=None):
    cap_path = OWN / 'candidate.json'
    assert digest(cap_path) == 'a2bafa968160fd2b36ef260ab75472af913ef56131a631d35f8bbf2c507eb298'
    cap = json.loads(cap_path.read_text())
    claim = json.loads(Path(scope_override).read_text()) if scope_override else CLAIM
    assert claim == CLAIM, 'unsupported scope strengthening or source contract alteration'
    reports = []
    for row, label, supplied in zip(cap['modules'], ['event-feed', 'event-cut'], [source_feed, source_cut]):
        source = Path(supplied) if supplied else PROD / (row['module'] + '.lean')
        assert digest(source) == row['source']['sha256'], 'source byte identity'
        out = AUDIT / label
        cfg = json.loads((out / 'config.json').read_text())
        strict = json.loads((out / 'prod-cert/strict-compile.json').read_text())
        compile_record = json.loads((out / 'cert/audit-compile.json').read_text())
        closure = json.loads((out / 'cert/closure.json').read_text())
        types = {r['name']: r for r in json.loads((out / 'cert/types.json').read_text())}
        assert compile_record['exit'] == 0
        assert len(strict) == 2 and all(r['exit'] == 0 for r in strict)
        assert strict[0]['source_sha256'] == digest(source)
        assert closure['axioms'] == 3
        assert len(closure['public']) == len(row['public_declarations'])
        assert set(closure['public']) == {r['name'] for r in row['public_declarations']}
        assert cfg['production_firsthit']['sha256'] == strict[0]['object_sha256']
        if label == 'event-feed':
            target = types[N + 'actual_dressed_photon_connected_feed']['type']
            for word in ['sourceNativeFrequencyPolarization', 'dressedCurrent',
                         'actualPreparationLeg', 'sourcePreparedPhotonAmplitude',
                         'sourcePhotonWholePair', 'prepared', 'event.cut']:
                assert word in target, ('lost actual feed field', word)
            weight = types[N + 'actual_preparation_weight']['type']
            assert 'actualPreparationScale' in weight and 'actualPreparationLeg' in weight
        else:
            target = types[N + 'actual_cut_free_sixth_ir_return']['type']
            for word in ['DressedEvent', 'cut', 'dressedStaticPolarization', 'Tendsto']:
                assert word in target, ('lost full IR contract', word)
            static_type = types['LowEnergy.GaussComposite.ActualDressedSylvester.dressedStaticPolarization']['type']
            assert 'Matrix (Fin 289) (Fin 289) ℂ' in static_type
            assert '∃L : Matrix (Fin 289) (Fin 289) ℂ,∀cut : ℕ' in source.read_text()
            assert 'physicalN3ResponseWindow' in types[N + 'actual_cut_free_physical_n3_window']['type']
        reports.append({'leaf': label, 'public': len(closure['public']), 'owned': len(closure['owned']),
                        'typed_consumers': len(closure['tests']), 'closure_nodes': closure['nodes'],
                        'opaque_all_read': closure['opaque_read'], 'source_path': str(source),
                        'source_sha256': digest(source), 'types_sha256': digest(out / 'cert/types.json')})
    return {'status': 'PASS_EXACT_EVENT_FEED_SCOPE_AND_BINDING', 'scope': claim, 'leaves': reports,
            'checks_are_artifact_and_claim_binding': True, 'domain_producer_replayed': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-feed')
    parser.add_argument('--source-cut')
    parser.add_argument('--scope-override')
    parser.add_argument('--output')
    args = parser.parse_args()
    try:
        result = check(args.source_feed, args.source_cut, args.scope_override)
        if args.output:
            Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result))
    except (AssertionError, OSError, KeyError) as error:
        print(json.dumps({'status': 'REJECT_EXACT_SCOPE_OR_BINDING', 'reason': str(error)}))
        raise SystemExit(1)
