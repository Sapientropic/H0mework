#!/usr/bin/env python3
"""Reuse unchanged verified obligations and recheck the migrated public intake."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

import compress as c

HERE = Path(__file__).resolve().parent
NIST = HERE.parents[2]
sys.path.insert(0, str(NIST))
PREVIOUS = NIST / 'evidence/readiness-source-compression-sc0001.json'
PREVIOUS_COMMIT = 'a75d59138f'
INPUT_EPOCH = 'c0ae9f2bd7'


def recorded_bytes(path, commit):
    relative = path.relative_to(c.ROOT).as_posix()
    return subprocess.check_output(['git', 'show', commit + ':' + relative], cwd=c.ROOT)


def unchanged_inputs(readiness):
    paths = [NIST / name for name in ('instrument.json', 'request.json', 'calibration-registry.json',
             'checks.py', 'test_real_family.py', 'nominal_environment_optimum.py',
             'evidence/lean-certification.json')]
    paths += [Path(readiness.rf.__file__).resolve(), c.ROOT / readiness.PRODUCTION, c.ROOT / readiness.CERTIFICATION]
    result = []
    for path in paths:
        c.require(path.read_bytes() == recorded_bytes(path, INPUT_EPOCH), 'unaffected_obligation_source_changed:' + str(path))
        result.append(c.frozen(path))
    c.require(all((NIST / name).is_file() for name in ('protocol.md', 'controller-capsule.md', 'access-record.md')),
              'protocol_inventory_changed')
    return result


def generate():
    c.require(PREVIOUS.read_bytes() == recorded_bytes(PREVIOUS, PREVIOUS_COMMIT), 'prior_actual_readiness_changed')
    prior = json.loads(PREVIOUS.read_text())
    readiness = c.module('_sc_actual_readiness_completion', NIST / 'readiness.py')
    nominal_module = c.module('_sc_unchanged_nominal_contract', NIST / 'nominal_environment_optimum.py')
    bindings = unchanged_inputs(readiness)
    expected = {'lean_family_and_certification': True, 'predictor_and_synthetic_regressions': True,
                'nominal_control_geometry': True, 'no_click_and_calibration_responsibilities': True,
                'protocol_and_budget_draft': True, 'nominal_apparatus_optimum': False}
    c.require(prior['schema'] == 'nist-real-readiness/v1' and prior['components'] == expected
              and all(type(v) is bool for v in prior['components'].values()), 'prior_component_obligations_not_verified')
    nominal = prior['nominal_replay']
    c.require(nominal['evidence_valid'] is True and nominal['production_eligible'] is True and nominal['verified'] is False
              and nominal['status'] == 'certified_deviation_exceeds_predeclared_band', 'prior_nominal_verdict_not_valid_negative')
    instrument = json.loads((NIST / 'instrument.json').read_text())
    c.require(nominal_module.consume_verified_cross({**nominal, 'status': 'verified'}, instrument) is False,
              'original_nominal_gate_contract_changed')
    compatible = c.module('_sc_current_public_intake', NIST / 'public_experiment_review_compatibility.py')
    compatible.legacy.verify_nominal_binding_tree(nominal['bindings'])
    compatible.legacy.verify_nominal_storage(nominal['bindings'])
    c.require(nominal['evaluator']['sha256'] == c.sha(NIST / 'nominal_environment_optimum.py'), 'nominal_evaluator_changed')
    public = readiness.public_experiment_review_investigation()
    compressed = readiness.public_source_compression_investigation()
    c.require(public.get('evidence_valid') is True and public.get('public_review_completed') is True
              and public.get('public_statistical_source_signature_certified') is True,
              'migrated_public_review_did_not_verify:' + str(public.get('reason', public.get('status'))))
    c.require(compressed.get('evidence_valid') is True and compressed.get('joint_95_source_domain_nonempty') is True
              and compressed.get('joint_95_source_domain_CH_N5_positive') is True, 'source_domain_did_not_verify')
    result = copy.deepcopy(prior)
    result.update(public_experiment_review=public, public_review_completed=True,
                  public_statistical_source_signature_certified=True, public_source_compression=compressed,
                  public_source_domain_compressed=True, joint_95_source_domain_nonempty=True,
                  joint_95_source_domain_CH_N5_positive=True, r0003_nist_ready=False,
                  status='review_completed_with_nominal_deviation')
    result['readiness_evidence_reuse'] = {
        'schema': 'nist-unchanged-obligation-reuse/v1', 'prior_actual_CLI_receipt': c.frozen(PREVIOUS),
        'unchanged_component_input_epoch': INPUT_EPOCH, 'unchanged_component_inputs': bindings,
        'completion_program': c.frozen(__file__), 'current_readiness_program': c.frozen(NIST / 'readiness.py'),
        'current_public_review_consumer': c.frozen(NIST / 'public_experiment_review_compatibility.py'),
        'original_nominal_negative_contract_reconsumed': True, 'nominal_sources_grid_or_Fock_reexecuted': False,
        'public_and_source_domain_consumers_reexecuted': True, 'raw_events_read': 0}
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    c.require(not args.output.exists(), 'completed_readiness_receipt_exists')
    result = generate()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'public_review_completed', 'public_source_domain_compressed',
        'joint_95_source_domain_nonempty', 'joint_95_source_domain_CH_N5_positive', 'r0003_nist_ready')}, sort_keys=True))
    return 0 if result['r0003_nist_ready'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
