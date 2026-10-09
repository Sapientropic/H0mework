"""Continue the paid current pump source to both original retarded cuts."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import subprocess
import time

import reissued_source_intake_rha0027 as paid
import prepared_retarded_gaussian_inlet as inlet
import retarded_receipt_trajectory_certificate as trajectory

HERE, ROOT = paid.HERE, paid.ROOT
SCIENCE = ('criterion-rha0027.md', 'criterion-rha0027.1.md', 'criterion-rha0027.2.md', 'criterion-rha0027.3.md', 'reissued_source_intake_rha0027.py',
    'retarded_inlet_resume_rha0027.py', 'gaussian_local_density_source.py',
    'test_density_checked_reuse_rha0027.py', 'test_reissued_source_intake_rha0027.py',
    'source-reissue-pumps-first-rha0025.json', 'retarded-local-density-first-rha0027.1.json')


def write(path, value):
    with Path(path).open('x') as handle:
        json.dump(value, handle, sort_keys=True); handle.write('\n')


def execute(freeze, output):
    bindings = {}
    for name in SCIENCE:
        path = HERE/name; data = path.read_bytes(); relative = path.relative_to(ROOT).as_posix()
        frozen = subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative])
        paid.require(data == frozen, 'continuation differs from scientific freeze: '+name)
        bindings[relative] = hashlib.sha256(data).hexdigest()
    output = Path(output).resolve()
    paid.require(output.is_relative_to(ROOT), 'the continuation output must remain in the workspace')
    output.mkdir(parents=True, exist_ok=False); started = time.monotonic()
    write(output/'attempt.json', {'schema': 'stage10-paid-source-retarded-inlet-attempt/rha0027',
        'scientific_freeze_commit': freeze, 'source_bindings': bindings})
    source = paid.restore_prepared(); raw = source.record()
    print('restored the same checked current pump source; no new pump residual', flush=True)
    old_path = paid.producer.original.INPUT
    with old_path.open('rb') as handle:
        paid.require(hashlib.file_digest(handle, 'sha256').hexdigest() == paid.producer.original.INPUT_SHA,
                     'the original density witness payload changed')
    with old_path.open() as handle: old_payload = json.load(handle)
    law = inlet.retarded.RetardedGaussianBSMSource(source._field)
    cuts = law.local_times(Q(law.record()['gate_seconds'][0]))
    banks = []; artifacts = []; completed = paid.completed_density_reports()
    for side, rows in enumerate(raw['source_issued_two_pump_factor_inlets']):
        old_bank = {item['factor_id']: item['complete_density_certificate']
                    for item in old_payload['density_witnesses'][side]}
        density = inlet.density.GaussianLocalDensitySource(source._field._pulses[side]); bank = []
        for item in rows:
            factor = item['factor_id']; old = old_bank[factor]; witness = old['untrusted_trial']
            paid.require(Q(witness['start_seconds']) == 0 and Q(witness['stop_seconds']) == cuts[side],
                         'the old witness must cover the actual source-issued retarded cut')
            trial = {'schema': inlet.density.SCHEMA+'/untrusted-curve', 'source_record': density.record(),
                'complete_initial_matrix': item['source_issued_next_phase']['complete_initial_local_factor'],
                'start_seconds': '0', 'stop_seconds': str(cuts[side]), 'mode_bits': witness['mode_bits'],
                'pieces': witness['pieces'], 'writer_correctness_assumed': False}
            prior = completed.get((side, factor))
            if prior is not None:
                paid.require(prior['untrusted_trial'] == trial and prior['source_record'] == density.record(),
                             'the paid local density must retain the exact current source and input')
                checked = density.verify(prior)
            else:
                checked = density.certify(trial, input_error=0, coefficient_bits=old['coefficient_bits'],
                                          envelope_order=old['envelope_order'])
            path = output/f'density-certificate-{side}-{factor[:12]}.json'; write(path, checked)
            artifacts.append({'side': side, 'factor_id': factor, 'path': path.relative_to(ROOT).as_posix(),
                'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
            bank.append({'factor_id': factor, 'complete_density_certificate': checked})
            print('checked full retarded local factor', side, factor[:12],
                  float(Q(checked['whole_trace_norm_error'])), 'reused' if prior is not None else 'fresh', flush=True)
        banks.append(bank)
    owned = inlet.PreparedRetardedGaussianInlet(source, law, banks,
        bits=old_payload['source_record']['scalar_bits'])
    output_path = output/'fresh-retarded-inlet.json'
    write(output_path, {'source_record': owned.record(), 'density_witnesses': banks})
    continuous = trajectory.RetardedReceiptTrajectoryCertificate.from_inlet(owned)
    summary = {'schema': 'stage10-paid-current-source-retarded-inlet/rha0027',
        'scientific_freeze_commit': freeze, 'source_bindings': bindings,
        'paid_pump_first_sha256': hashlib.sha256(paid.FIRST.read_bytes()).hexdigest(),
        'source_retarded_local_cuts_seconds': list(map(str, cuts)), 'density_certificate_artifacts': artifacts,
        'fresh_inlet': {'path': output_path.relative_to(ROOT).as_posix(), 'bytes': output_path.stat().st_size,
            'sha256': hashlib.sha256(output_path.read_bytes()).hexdigest()},
        'whole_retarded_gate_input_error': owned.record()['whole_retarded_gate_input_error'],
        'source_owned_continuous_trajectory_constructed': True,
        'continuous_source_schema': continuous.record()['schema'], 'complete_local_residual_count': 10,
        'new_pump_solver_or_residual_executed': False, 'old_density_endpoint_used_as_free_input': False,
        'original_trajectory_counterflow_and_Mark_targets_retained': True,
        'generation1_asserted': False, 'complete_gate_certificate_executed': False,
        'actual_hardware_member_asserted': False, 'actual_hardware_uniquely_identified': False,
        'controller_advance': False, 'seconds': time.monotonic()-started}
    write(output/'summary.json', summary)
    print(json.dumps({'source_retarded_local_cuts_seconds': summary['source_retarded_local_cuts_seconds'],
        'whole_retarded_gate_input_error': float(Q(summary['whole_retarded_gate_input_error'])),
        'source_owned_continuous_trajectory_constructed': True, 'seconds': summary['seconds']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    args = parser.parse_args(); execute(args.freeze, args.output)
