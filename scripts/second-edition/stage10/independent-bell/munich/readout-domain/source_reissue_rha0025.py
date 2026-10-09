"""Recheck the original raw-source witnesses under the current constructors.

Only source-owned primitive declarations and untrusted curves cross the old
binding boundary.  No saved Ready, pump or gate endpoint becomes a seed.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import subprocess
import time

import reference_atomic_clock_source as reference
import reference_local_phase_source as local
import fourier_reference_local_programme_source as programme
import prepared_gaussian_field_source as prepared
import prepared_retarded_gaussian_inlet as inlet
import retarded_count_rotating_run_rha0024 as original

HERE = Path(__file__).resolve().parent
ROOT = original.ROOT
WITNESS = ROOT/'ComputeNode/state/bell-retarded-kernels/source-inlet-closure-339e2c7617040b10/original-two-pump-witnesses.json'
WITNESS_SHA = 'e638e87134e1608511e39b0a846c8aa6c4096a5dc16a2cde45d6ac47da0e5f4f'
SCIENCE = ('source_reissue_rha0025.py', 'criterion-rha0025.md', 'test_source_reissue_rha0025.py')


def require(value, reason):
    if not value:
        raise ValueError(reason)


def mathematical_record(value):
    """Compare every source field except obsolete executable-file attestations."""
    if type(value) is dict:
        return {key: mathematical_record(item) for key, item in value.items() if key != 'source_bindings'}
    if type(value) is list:
        return [mathematical_record(item) for item in value]
    return value


def fresh_reference_source(record):
    require(type(record) is dict and record.get('schema') == reference.SCHEMA,
            'the original complete reference declaration is required')
    mother = reference.native.ready.PersistentReadyMother.from_record(
        record['normalized_native_assembler']['original_PRM_source'])
    frame = reference.native.NativeToneFrame(mother)
    clock = record['reference_clock']
    source = reference.ReferenceAtomicClockSource(frame,
        aperture_source=reference._read_aperture(record['same_lambda_aperture_source']),
        physical_duration_seconds=record['physical_duration_seconds'],
        pi_terms=clock['terms'], clock_bits=clock['bits'])
    require(mathematical_record(source.record()) == mathematical_record(record),
            'an original primitive, action, optical parameter, clock or source scope changed')
    return source


def recheck_ready(source, old_ready):
    require(type(source) is reference.ReferenceAtomicClockSource,
            'the freshly generated closed reference source is required')
    candidate = old_ready['physical_CP_certificate']
    report = source.certify(candidate['untrusted_pieces'], physical_time=candidate['physical_time'], **candidate['precision'])
    return source.first_poll_ready(report)


def recheck_pumps(source, old_certificates, templates):
    raw = source.record()['reference_local_parent']; generated = []
    require(type(old_certificates) in (list, tuple) and len(old_certificates) == 2 and len(templates) == 2,
            'both original pump curve banks are required')
    for side, inventory in enumerate(raw['local_factor_inventory']):
        old = {item['factor_id']: item for item in old_certificates[side]}
        require(set(old) == {item['factor_id'] for item in inventory} and len(old) == len(old_certificates[side]),
                'old curves must cover every newly source-generated factor exactly once')
        rows = []
        for item in inventory:
            factor_id = item['factor_id']; checked = []
            candidates = old[factor_id]['complete_phase_certificates']
            require(len(candidates) == 2, 'exactly both original pump witnesses are required')
            for index, candidate in enumerate(candidates):
                phase = source.phase_source(side, factor_id, checked, templates[side])
                require(phase.record()['phase_index'] == index, 'the source issued a different pump phase')
                precision = candidate['precision']
                if 'untrusted_curve' in candidate:
                    report = phase.certify(candidate['untrusted_curve'], **precision)
                else:
                    require('untrusted_shared_witness' in candidate, 'an original raw pump curve is missing')
                    report = programme._certify_shared_phase(phase, candidate['untrusted_shared_witness'], templates[side][index], precision)
                checked.append(report)
                print('checked original pump', side, factor_id[:12], index, flush=True)
            rows.append({'factor_id': factor_id, 'complete_phase_certificates': checked})
        generated.append(rows)
    return generated


def bound_source(freeze):
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', freeze, 'HEAD'], check=True)
    paths = [HERE/name for name in SCIENCE]
    modules = (reference, local, programme, prepared, inlet, original)
    paths += [Path(module.__file__) for module in modules]
    result = {}
    for path in paths:
        relative = path.relative_to(ROOT).as_posix(); data = path.read_bytes()
        frozen = subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative])
        require(data == frozen, 'executed source differs from scientific freeze: '+relative)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def write(path, value):
    with Path(path).open('x') as handle:
        json.dump(value, handle, sort_keys=True); handle.write('\n')


def execute(freeze, output, stage='pumps'):
    require(stage in ('ready', 'pumps', 'inlet'), 'an explicit source recheck stage is required')
    bound = bound_source(freeze); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    write(output/'attempt.json', {'schema': 'stage10-original-raw-source-reissue-attempt/rha0025',
        'scientific_freeze_commit': freeze, 'source_bindings': bound, 'stage': stage,
        'source_payload_sha256': original.INPUT_SHA, 'pump_witness_payload_sha256': WITNESS_SHA})
    law = original.source_law(original.INPUT)
    old_field = law['complete_driven_field_source']
    parent = old_field['Gaussian_source_legs'][0]['reference_local_parent']
    old_reference = parent['reference_native_source_record']
    fresh = fresh_reference_source(old_reference)
    print('fresh original reference generated from its primitive and raw controls', flush=True)
    ready = recheck_ready(fresh, parent['reference_first_poll_ready'])
    write(output/'fresh-reference-ready.json', ready)
    print('complete original first-poll CP curve rechecked', flush=True)
    summary = {'schema': 'stage10-original-raw-source-reissue/rha0025',
        'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'source_payload_sha256': original.INPUT_SHA, 'stage': stage,
        'source_primitive_regenerated': True, 'all_mathematical_reference_fields_preserved': True,
        'old_executable_bindings_relabelled': False, 'old_ready_endpoint_used_as_input': False,
        'same_original_Ready_matrix_regenerated': ready['generated_first_ready_poststate'] == parent['reference_first_poll_ready']['generated_first_ready_poststate'],
        'fresh_Ready_error': ready['first_poll_joint_error'],
        'fresh_Ready_sha256': hashlib.sha256((output/'fresh-reference-ready.json').read_bytes()).hexdigest(),
        'actual_hardware_member_asserted': False, 'actual_hardware_uniquely_identified': False,
        'controller_advance': False, 'solver_executed': False}
    if stage != 'ready':
        with WITNESS.open('rb') as handle:
            require(hashlib.file_digest(handle, 'sha256').hexdigest() == WITNESS_SHA, 'original pump witness bytes changed')
        with WITNESS.open() as handle: witness = json.load(handle)
        old_parent = witness['programme_source_record']['reference_local_parent']
        require(mathematical_record(old_parent['reference_native_source_record']) == mathematical_record(old_reference),
                'the two original source declarations do not share their primitive occurrence')
        raw_plans = [[item['raw_controls'] for item in side] for side in old_parent['source_generated_local_plans']]
        new_parent = local.ReferenceLocalPhaseSource(fresh, ready, raw_plans)
        new_programme = programme.FourierReferenceLocalProgrammeSource(new_parent)
        certificates = recheck_pumps(new_programme, witness['prefix_certificates'], witness['shared_phase_templates'])
        pulses = tuple(prepared.driven.gaussian.GaussianAtomicPulseSource(new_parent, side,
            **{key: old_field['Gaussian_source_legs'][side][key] for key in
               ('sigma_squared_seconds', 'centre_seconds', 'duration_seconds', 'phase_radians')}) for side in (0, 1))
        photon = prepared.driven.DrivenGaussianFieldSource(*pulses,
            flight_seconds=old_field['flight_seconds'], emission_origins_seconds=old_field['emission_origins_seconds'],
            gate_seconds=law['gate_seconds'])
        prepared_source = prepared.PreparedGaussianFieldSource(new_programme, certificates, witness['shared_phase_templates'], photon)
        write(output/'fresh-prepared-source.json', prepared_source.record())
        write(output/'fresh-pump-certificates.json', certificates)
        summary.update(complete_two_pump_prefix_rechecked=True,
            fresh_prepared_source_sha256=hashlib.sha256((output/'fresh-prepared-source.json').read_bytes()).hexdigest(),
            old_pump_endpoint_used_as_input=False, source_tensor_term_count=len(prepared_source._terms))
        if stage == 'inlet':
            with original.INPUT.open() as handle: old_inlet = json.load(handle)
            banks = []
            source_raw = prepared_source.record(); retarded = inlet.retarded.RetardedGaussianBSMSource(photon)
            cuts = retarded.local_times(Q(law['gate_seconds'][0]))
            for side, items in enumerate(source_raw['source_issued_two_pump_factor_inlets']):
                old_bank = {item['factor_id']: item['complete_density_certificate'] for item in old_inlet['density_witnesses'][side]}
                density_source = inlet.density.GaussianLocalDensitySource(pulses[side]); checked_bank = []
                for item in items:
                    factor_id = item['factor_id']; old = old_bank[factor_id]; curve = old['untrusted_trial']
                    initial = item['source_issued_next_phase']['complete_initial_local_factor']
                    require(Q(curve['start_seconds']) == 0 and Q(curve['stop_seconds']) == cuts[side],
                            'the old density witness must cover this original retarded cut')
                    trial = {'schema': inlet.density.SCHEMA+'/untrusted-curve', 'source_record': density_source.record(),
                        'complete_initial_matrix': initial, 'start_seconds': '0', 'stop_seconds': str(cuts[side]),
                        'mode_bits': curve['mode_bits'], 'pieces': curve['pieces'], 'writer_correctness_assumed': False}
                    report = density_source.certify(trial, input_error=0, coefficient_bits=old['coefficient_bits'],
                        envelope_order=old['envelope_order'])
                    checked_bank.append({'factor_id': factor_id, 'complete_density_certificate': report})
                    print('checked original full density', side, factor_id[:12], flush=True)
                banks.append(checked_bank)
            new_inlet = inlet.PreparedRetardedGaussianInlet(prepared_source, retarded, banks,
                bits=old_inlet['source_record']['scalar_bits'])
            write(output/'fresh-source-issued-inlet.json', {'source_record': new_inlet.record(), 'density_witnesses': banks})
            summary.update(complete_retarded_inlet_rechecked=True,
                fresh_inlet_sha256=hashlib.sha256((output/'fresh-source-issued-inlet.json').read_bytes()).hexdigest(),
                fresh_inlet_error=new_inlet.record()['whole_retarded_gate_input_error'],
                old_density_endpoint_used_as_input=False)
    summary['seconds'] = time.monotonic()-started
    write(output/'summary.json', summary)
    print(json.dumps(summary, sort_keys=True), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    parser.add_argument('--stage', choices=('ready', 'pumps', 'inlet'), default='pumps')
    args = parser.parse_args(); execute(args.freeze, args.output, args.stage)
