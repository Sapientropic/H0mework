"""Raw AOM programmes act on a full stopped BSM input before the CEM.

The inherited full source residual checker consumes every pair coordinate.
No ideal herald, qubit projection or target measurement effect is supplied.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import joint_fluorescence_presence as joint
import raw_command_family as commands
import cem_pair_source as cem


def _norm_upper(matrix):
    result = Q(0)
    for value in matrix.values():
        for part in (value.real, value.imag):
            center, error = full.radical_midpoint(part, 160)
            result += abs(center)+error
    return result


class PairMeasurementSource:
    def __init__(self, transfer_a, transfer_b, templates_a, templates_b, *,
                 backgrounds, fragment_efficiencies, command_bits=240):
        self.transfers = (commands.transfer_matrix(transfer_a), commands.transfer_matrix(transfer_b))
        self.templates = tuple(tuple(full.Segment.from_record(segment.record()) for segment in raw)
                               for raw in (templates_a, templates_b))
        self.command_bits = command_bits
        self.detector = cem.PairCEMInstrument(backgrounds=backgrounds, fragment_efficiencies=fragment_efficiencies)
        self.programmes = tuple(tuple(commands.compile_commands(transfer, templates, angle, command_bits)
                                      for angle in commands.SIDE_ANGLES[side])
                                for transfer, templates, side in zip(self.transfers, self.templates, ('alice', 'bob')))
        for first in self.programmes[0]:
            for second in self.programmes[1]:
                if len(first.segments) != len(second.segments) or any(
                        a.duration != b.duration for a, b in zip(first.segments, second.segments)):
                    raise ValueError('two measurement programmes require the same raw time partition')

    def compile(self, settings):
        if type(settings) is not tuple or len(settings) != 2 or any(
                type(bit) is not int or bit not in (0, 1) for bit in settings):
            raise ValueError('two source-owned nominal AOM command bits required')
        return tuple(self.programmes[side][bit] for side, bit in enumerate(settings))

    def sources(self, settings):
        first, second = self.compile(settings)
        return tuple(joint.JointCounterGenerator(a, b, threshold=1, background_rate=0,
                                                 collection=((0, 0, 0, 0, 0, 0),))
                     for a, b in zip(first.segments, second.segments))

    def certify(self, initial, *, trap_histories, settings, trial_families, input_error=0,
                mode_bits=60, coefficient_bits=160, exponential_bits=160):
        matrix = cem._poststate(initial, trap_histories)
        if type(trial_families) is not list or len(trial_families) != len(self.templates[0]):
            raise ValueError('complete raw measurement phase trial family required')
        first, second = self.compile(settings)
        error, duration, certificates = full.nonnegative(input_error), Q(0), []
        for index, (source, pieces) in enumerate(zip(self.sources(settings), trial_families)):
            # Exact nominal command substitution acts on this same state; no normalized reset.
            payment = sum((Q(program.hamiltonian_certificates[index]['cptp_duhamel_trace_norm_error'])
                           for program in (first, second)), Q(0))*(_norm_upper(matrix)+error)
            report = channel.certify(source, matrix, pieces, upstream_error=error+payment,
                                     mode_bits=mode_bits, coefficient_bits=coefficient_bits,
                                     exponential_bits=exponential_bits)
            if report['at_least_N']['poststate_center']:
                raise ValueError('unobserved atomic phase cannot generate a photon-counter event')
            certificates.append({'command_substitution_payment': str(payment), 'source_certificate': report})
            matrix, error = channel.poststate(report)
            duration += source.duration
        image = self.detector.apply(matrix, trap_histories=trap_histories, input_error=error)
        return {'schema': 'stage10-full-pair-measurement-programme/v1', 'raw_source': self.record(),
                'settings': settings, 'initial_state': channel._input_record(cem._poststate(initial, trap_histories)),
                'parent_trap_histories': trap_histories, 'upstream_error': str(full.nonnegative(input_error)),
                'phase_certificates': certificates, 'duration': str(duration),
                'complete_poststate': matrix, 'trace_norm_error': error, 'cem_image': image,
                'ideal_Bell_state_substituted': False, 'qubit_reprojection_performed': False,
                'actual_hardware_uniquely_identified': False, 'controller_advance': False}

    def verify(self, report):
        if type(report) is not dict or report.get('raw_source') != self.record():
            raise ValueError('same raw measurement source certificate required')
        families = [item['source_certificate']['trial_pieces'] for item in report['phase_certificates']]
        phase = report['phase_certificates'][0]['source_certificate']
        bound = type(self).from_record(report['raw_source'])
        expected = bound.certify(channel._read_input(report['initial_state'], joint.DIMENSION),
                                trap_histories=report['parent_trap_histories'], settings=report['settings'],
                                trial_families=families, input_error=report['upstream_error'],
                                mode_bits=phase['mode_bits'], coefficient_bits=phase['coefficient_bits'],
                                exponential_bits=phase['exponential_bits'])
        if expected != report:
            raise ValueError('raw full pair measurement residual certificate mismatch')
        return True

    def predict(self, initial, *, trap_histories, settings, input_error=0,
                rtol=1e-10, atol=1e-13, max_coordinates=50000):
        import fluorescence_channel_search as search
        matrix, error, families = cem._poststate(initial, trap_histories), full.nonnegative(input_error), []
        for source in self.sources(settings):
            report = search.predict(source, matrix, upstream_error=error, rtol=rtol, atol=atol,
                                    max_coordinates=max_coordinates)
            families.append(report['trial_pieces'])
            matrix, error = channel.poststate(report)
        return self.certify(initial, trap_histories=trap_histories, settings=settings,
                            trial_families=families, input_error=input_error)

    def record(self):
        return {'schema': 'rb87-full-pair-measurement-source/v1',
                'transfers': [[[value.serialize() for value in row] for row in transfer] for transfer in self.transfers],
                'templates': [[segment.record() for segment in raw] for raw in self.templates],
                'command_bits': self.command_bits, 'detector': self.detector.record(),
                'commands': [list(commands.SIDE_ANGLES[side]) for side in ('alice', 'bob')],
                'physical_dimension': joint.DIMENSION, 'source_input': 'complete stopped BSM state with cohort history',
                'source_generates_effect_instead_of_accepting_target': True,
                'actual_control_clock_record_square_certified': False, 'controller_advance': False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get('schema') != 'rb87-full-pair-measurement-source/v1':
            raise ValueError('raw full pair measurement source record required')
        transfers = tuple(tuple(tuple(channel._complex_record(value) for value in row) for row in transfer)
                          for transfer in record['transfers'])
        templates = tuple(tuple(full.Segment.from_record(segment) for segment in raw) for raw in record['templates'])
        detector = cem.PairCEMInstrument.from_record(record['detector'])
        source = cls(*transfers, *templates, backgrounds=detector.backgrounds,
                     fragment_efficiencies=detector.efficiencies, command_bits=record['command_bits'])
        if source.record() != record:
            raise ValueError('raw measurement source identity or scope changed')
        return source
