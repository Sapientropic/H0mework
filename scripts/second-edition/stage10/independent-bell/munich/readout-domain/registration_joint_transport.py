"""Raw flight/window registration realizers of the paid full joint member.

Only original raw controls and detector parameters seed the generated source.
The original confidence receipt is transported by a complete operator
intertwiner, without re-scoring events or choosing new statistical parameters.
"""
from dataclasses import replace
from fractions import Fraction as Q
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

import atomic_dipole as dipole
import atomic_full_forward as full
import mode_prefix_intake as paid
import raw_command_family as commands
import registration_window_domain as domain
import window_cem_source as window


BASE = Path(__file__).resolve().parent
OWN = ('window_cem_source.py', 'test_window_cem_source.py', 'registration_window_domain.py',
       'test_registration_window_domain.py', 'registration_joint_transport.py',
       'test_registration_joint_transport.py', 'criterion-registration-wr0001.md')


def frozen_bindings():
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=full.ROOT, text=True).strip()
    result = []
    for name in OWN:
        path = BASE/name
        raw = paid.frozen(path, commit)
        result.append({'path': str(path.relative_to(full.ROOT)), 'sha256': hashlib.sha256(raw).hexdigest()})
    return commit, result


def _side_programs(run, template):
    result = []
    for index, side in enumerate(('alice', 'bob')):
        transfer = tuple(tuple(dipole.ComplexRadical(Q.from_float(real), Q.from_float(imag))
                               for real, imag in row) for row in run['raw_transfers'][index])
        result.append(tuple(commands.compile_commands(transfer, (template,), angle, 240)
                            for angle in commands.SIDE_ANGLES[side]))
    return tuple(result)


def source_for_settings(run, template, settings, *, geometry, registration_coordinates=((0, 0), (0, 0))):
    """A source clock representative plus coverage valid on its whole enclosure."""
    programs = _side_programs(run, template)
    unit = Q(geometry['seconds_per_source_unit_enclosure'][1])
    ns = domain.NS
    deadlines = (650*ns/unit, 809*ns/unit)
    terminal = max(deadlines)
    waveforms, registrations, backgrounds = [], [], []
    for index, setting in enumerate(settings):
        program = programs[index][setting]
        pulse = program.segments[0]
        d, eta = map(Q.from_float, run['raw_parameters'][8+2*index:10+2*index])
        face = domain.registration_face(eta)
        probabilities = domain.source_registration_point(face, *registration_coordinates[index])
        ion_flight = (400 if index == 0 else 550)*ns
        e_window = (3*ns, (243 if index == 0 else 163)*ns)
        i_window = ((330 if index == 0 else 505)*ns, (570 if index == 0 else 725)*ns)
        registrations.append(window.FragmentRegistration(probabilities, 3*ns/unit, ion_flight/unit,
                                     tuple(t/unit for t in e_window), tuple(t/unit for t in i_window)))
        idle = replace(pulse, duration=terminal-pulse.duration, r=0, c=0,
                       fields_r=dict.fromkeys(dipole.Q_COMPONENTS, 0), fields_c=dict.fromkeys(dipole.Q_COMPONENTS, 0),
                       ion_rates=dict.fromkeys(full.EXCITED, 0))
        waveforms.append((pulse, idle))
        backgrounds.append(d)
    return window.WindowCEMSource(*waveforms, registrations=tuple(registrations), backgrounds=tuple(backgrounds),
                       logic_deadlines=deadlines, seconds_per_unit=unit)


def derive():
    prior = domain.paid_joint_domains()
    freeze = prior['prior_full_joint_membership']['science_freeze']
    candidate = json.loads(paid.frozen(BASE/'hardware-inverse-first-hi0002.json', freeze))
    mode = json.loads(gzip.decompress(paid.frozen(BASE/'mode-forward-mi0001.json.gz', freeze)))
    template = full.Segment.from_record(candidate['raw_template'])
    reductions = []
    for run, old in zip(candidate['runs'], mode['runs']):
        if run['run'] != old['run']:
            raise ValueError('original raw source run order changed')
        programs = _side_programs(run, template)
        for index, side in enumerate(('alice', 'bob')):
            for setting in (0, 1):
                saved = next(item for item in old['settings'] if (item['side'], item['setting']) == (side, setting))
                binding = saved['witness']
                path = BASE/binding['path']
                if path.parent != BASE or path.name != binding['path']:
                    raise ValueError('old mode witness path outside source corridor')
                raw = path.read_bytes()
                if len(raw) != binding['bytes'] or hashlib.sha256(raw).hexdigest() != binding['sha256']:
                    raise ValueError('old mode witness identity changed')
                decoded = gzip.decompress(raw)
                if hashlib.sha256(decoded).hexdigest() != binding['decoded_sha256']:
                    raise ValueError('old mode decoded source changed')
                witness = json.loads(decoded)
                if witness['raw_program'] != programs[index][setting].segments[0].record():
                    raise ValueError('window source and paid raw atomic action differ')
        for a in (0, 1):
            for b in (0, 1):
                source = source_for_settings(run, template, (a, b), geometry=prior['window_geometry'])
                reduction = window.constant_gate_reduction(source)
                reductions.append({'run': run['run'], 'settings': [a, b], 'source_reduction': reduction})
                print(json.dumps({'run': run['run'], 'settings': [a, b],
                                  'columns': reduction['local_basis_columns_checked']}), flush=True)
    return {'schema': 'stage10-raw-registration-joint-transport/v1', 'verified': True,
            'paid_source_domain': prior, 'source_reductions': reductions,
            'raw_registration_joint_member_realizers_generated': True,
            'old_joint_probability_law_preserved_by_full_operator_reduction': True,
            'time_unit_representative_role': 'conservative clock chart; not a rounded value of pi or actual clock calibration',
            'coverage_holds_for_whole_normalization_enclosure': True,
            'clock_record_square_certified': False, 'actual_hardware_uniquely_identified': False,
            'new_confidence_budget_spent': False, 'archive_files_read': 0,
            'new_numerical_solves': 0, 'new_statistical_executions': 0, 'controller_advance': False}


def exclusive(path, data):
    raw = (json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2)+'\n').encode()
    with Path(path).open('xb') as stream:
        stream.write(gzip.compress(raw, mtime=0) if str(path).endswith('.gz') else raw)


def execute(output):
    commit, bindings = frozen_bindings()
    output = Path(output)
    attempt = output.with_name(output.name+'-attempt.json')
    if output.exists() or attempt.exists():
        raise FileExistsError('registered source transport first already exists')
    exclusive(attempt, {'schema': 'stage10-registration-joint-transport-attempt/v1',
                        'science_freeze': commit, 'source_bindings': bindings})
    report = {'science_freeze': commit, 'source_bindings': bindings}
    try:
        report.update(derive())
    except Exception as error:
        report.update(verified=False, status='rejected', error_type=type(error).__name__, error=str(error))
        exclusive(output, report)
        raise
    exclusive(output, report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    execute(parser.parse_args().output)
