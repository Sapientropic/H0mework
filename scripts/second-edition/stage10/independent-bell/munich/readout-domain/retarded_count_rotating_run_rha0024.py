"""Apply the frozen rotating chart to the original declared source coefficients.

Only primitive source declarations are reconstructed.  Cached density
endpoints and their old executable bindings are not admitted by this run.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import mmap
import subprocess

import retarded_count_rotating_source as code
import retarded_count_rotating_independent as independent

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p/'ComputeNode').is_dir() and (p/'Verification').is_dir())
INPUT = ROOT/'ComputeNode/state/bell-retarded-kernels/local-source-inlet-339e2c7617040b10/source-issued-inlet.json'
INPUT_SHA = 'e9667f34d6d8743ee9a7c3baaf49d7210ab637f37d04255a46141483d35e5128'
SCIENCE = ('retarded_count_rotating_source.py', 'retarded_count_rotating_independent.py',
           'retarded_count_rotating_run_rha0024.py', 'criterion-rha0024.md', 'test_retarded_count_rotating_source.py')


def source_law(path):
    with path.open('rb') as handle:
        code.count.require(hashlib.file_digest(handle, 'sha256').hexdigest() == INPUT_SHA,
                           'the original source-issued payload bytes changed')
        with mmap.mmap(handle.fileno(), 0, access=mmap.ACCESS_READ) as data:
            key = b'"retarded_detector_law":'
            offset = data.find(key)
            code.count.require(offset >= 0, 'original retarded law declaration missing')
            start = offset+len(key)
            while data[start:start+1] in (b' ', b'\n', b'\r', b'\t'): start += 1
            size = 1 << 20
            while size <= 64 << 20:
                try:
                    record, _ = json.JSONDecoder().raw_decode(data[start:start+size].decode())
                    return record
                except json.JSONDecodeError:
                    size *= 2
            raise ValueError('bounded original source-law declaration exceeded 64 MiB')


def scientific_bindings(freeze):
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', freeze, 'HEAD'], check=True)
    result = {}
    for name in SCIENCE:
        path = HERE/name; data = path.read_bytes(); relative = path.relative_to(ROOT).as_posix()
        frozen = subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative])
        code.count.require(data == frozen, 'scientific source changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def execute(freeze, output):
    bound = scientific_bindings(freeze)
    output = Path(output)
    code.count.require(not output.exists(), 'the first receipt is immutable')
    attempt = output.with_suffix('.attempt.json')
    with attempt.open('x') as handle:
        json.dump({'schema': 'stage10-rotating-count-coefficients-attempt/rha0024',
                   'scientific_freeze_commit': freeze, 'source_bindings': bound,
                   'source_payload_sha256': INPUT_SHA, 'result_written': False}, handle, sort_keys=True)
    law = source_law(INPUT); field = law['complete_driven_field_source']
    pulses = field['Gaussian_source_legs']; origins = tuple(map(Q, field['emission_origins_seconds']))
    code.count.require(len(origins) == 2 and origins[0] == origins[1], 'original equal excitation origins required')
    owner = code.excitation.atomic.MunichAtomicProgramme.from_record(pulses[0]['working_atomic_owner'])
    fresh, equalities = [], []
    keys = ('complete_static_H_per_second', 'complete_natural_R_per_second', 'source_raising_operator_per_second',
            'carrier_angular_frequency_per_second', 'original_physical_natural_jumps')
    for side, pulse in enumerate(pulses):
        code.count.require(owner.record() == pulse['working_atomic_owner'] and Q(pulse['phase_radians']) == 0,
                           'the original same-owner zero raw phase declaration is required')
        original = pulse['original_constant_excitation_controls']; controls = original['raw_controls']
        phase = owner.phase('excitation', side, Q(controls['duration_seconds']),
                            tuple(code.excitation.atomic.Drive.from_record(d) for d in controls['drives']))
        code.count.require(phase.record() == original['source_phase'], 'original raw excitation declaration changed')
        plan = {**original, 'source_phase': phase.record()}
        shape = {k: pulse[k] for k in ('sigma_squared_seconds', 'centre_seconds')}
        regenerated = code.excitation._primitive(owner, plan, shape, side, Q(pulse['duration_seconds']))
        code.count.require(all(regenerated[k] == pulse[k] for k in keys),
                           'fresh full source coefficients do not reproduce the original declared law')
        fresh.append(regenerated); equalities.append({'side': side, 'exact_primitive_fields': list(keys)})
    g0, g1 = (Q(t)-origins[0] for t in law['gate_seconds'])
    raw = {'working_atomic_owner': owner.record(), 'working_common_optical_source': field['working_common_optical_source'],
           'source_generated_zero_line_chart_pulses': fresh, 'flight_seconds': field['flight_seconds'],
           'source_gate_offsets_from_pump_end_seconds': list(map(str, (g0, g1)))}
    grades = code.count.grading(fresh, raw['working_common_optical_source'])
    import retarded_gate_common_phase_independent as grade_check
    grade_check.check_grading(fresh, raw['working_common_optical_source'], grades)
    samples = []
    for t in (g0, (g0+g1)/2, g1):
        pair = code.gate_primitives(raw, t, 0)
        for side, report in enumerate(pair):
            independent.check_primitive(fresh[side], t, field['flight_seconds'][side], 0, report)
        samples.append({'source_detector_offset_seconds': str(t),
                        'source_scalar_H_error_upper_per_second': [r['H_scalar_operator_error_upper_per_second'] for r in pair],
                        'full_H_K_and_bath_independently_checked': True})
    inlet = code.inlet_protocol(raw, 0); independent.check_inlet_protocol(raw, 0, inlet)
    norms = []
    for side, pulse in enumerate(fresh):
        physical = code.gaussian._matrix(pulse['complete_static_H_per_second'])
        rotating = code.gaussian._matrix(code.gate_primitives(raw, g0, 0)[side]['source_rotating_static_H_per_second'])
        before, after = code.gaussian._norm(physical, 192), code.gaussian._norm(rotating, 192)
        norms.append({'side': side, 'physical_static_operator_norm_upper': str(before),
                      'rotating_static_operator_norm_upper': str(after),
                      'ratio_of_source_norm_bounds': str(before/after) if after else None})
    result = {'schema': 'stage10-original-source-rotating-count-coefficients/rha0024',
        'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'source_payload': {'path': INPUT.relative_to(ROOT).as_posix(), 'sha256': INPUT_SHA},
        'fresh_primitive_equalities': equalities, 'source_grading': grades,
        'source_gate_offsets_seconds': raw['source_gate_offsets_from_pump_end_seconds'],
        'source_local_inlet_intervals_seconds': [r['source_local_interval_seconds'] for r in inlet['local_source_flows']],
        'source_samples': samples, 'source_static_norm_bounds': norms,
        'scope': {'original_declared_primitive_coefficients_regenerated': True,
                  'cached_density_endpoint_used_as_source': False, 'old_executable_binding_relabelled': False,
                  'typed_next_high_poll_occurrence_applied': False, 'inlet_or_gate_numerical_certificate_executed': False,
                  'actual_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False,
                  'event_archives_read': False, 'controller_advance': False}}
    with output.open('x') as handle:
        json.dump(result, handle, sort_keys=True, indent=2); handle.write('\n')
    print(json.dumps({'output': str(output), 'source_gate_offsets_seconds': result['source_gate_offsets_seconds'],
                      'static_norm_bound_ratios': [float(Q(r['ratio_of_source_norm_bounds'])) for r in norms]}, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--freeze', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    execute(args.freeze, args.output)
