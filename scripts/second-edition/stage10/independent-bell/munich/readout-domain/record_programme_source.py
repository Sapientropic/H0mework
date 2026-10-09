"""Stopped apparatus action -> local record semantics with raw encoder variables.

The original parser owns row numbers and byte identity.  This source supplies
their physical-field restriction; it does not regenerate the original CSV.
Clock, latency and bit polarity remain inverse variables in this model family.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

import atomic_full_forward as full
import cem_pair_source as cem
import fluorescence_channel as channel
import history_feed as history
import measurement_programme as measurement
import stopped_bsm_programme as stopped


# The paid complete local observers retain these literal flag/comment tokens.
MODES = {'valid': ('no', ' '), 'cem-off': ('yes', 'CEMs off'), 'maintenance': ('yes', 'Maintenance')}


@dataclass(frozen=True)
class LabEncoder:
    sample_period: Q
    sample_phase: Q
    uid_origin: int
    uid_stride: int
    unix_origin_ms: Q
    request_latency: Q = Q(0)
    write_latency: Q = Q(0)
    click_token: str = '1'
    setting_zero_token: str = '0'

    def __post_init__(self):
        for name in ('sample_period', 'sample_phase', 'unix_origin_ms', 'request_latency', 'write_latency'):
            object.__setattr__(self, name, full.exact(getattr(self, name)))
        if self.sample_period <= 0 or self.request_latency < 0 or self.write_latency < 0:
            raise ValueError('positive sample period and nonnegative causal latency required')
        if type(self.uid_origin) is not int or type(self.uid_stride) is not int or self.uid_stride <= 0:
            raise ValueError('raw integer UID origin and positive stride required')
        if self.click_token not in ('0', '1') or self.setting_zero_token not in ('0', '1'):
            raise ValueError('raw binary result and setting token maps required')

    def sample_at(self, signal_return_time):
        request = full.exact(signal_return_time)+self.request_latency
        quotient = (request-self.sample_phase)/self.sample_period
        index = -(-quotient.numerator//quotient.denominator)
        selected_time = self.sample_phase+index*self.sample_period
        uid = self.uid_origin+self.uid_stride*index
        if uid < 0:
            raise ValueError('raw encoder emitted a negative public UID')
        return selected_time, uid

    def record(self):
        return {name: str(getattr(self, name)) if name not in ('uid_origin', 'uid_stride', 'click_token', 'setting_zero_token')
                else getattr(self, name) for name in self.__dataclass_fields__}


@dataclass(frozen=True)
class RecordBranch:
    clicks: tuple
    local_fields: tuple
    complete_poststate: dict
    next_trap_input: dict
    source_journal: tuple
    shared_trace_norm_error: Q


@dataclass(frozen=True)
class RecordImage:
    branches: tuple
    remaining_pair: dict
    joint_trace_norm_error: Q
    source_record: dict


class RecordWriterSource:
    def __init__(self, encoders, *, seconds_per_unit):
        if type(encoders) is not tuple or len(encoders) != 2 or any(type(item) is not LabEncoder for item in encoders):
            raise ValueError('two raw side-owned encoder sources required')
        self.encoders = encoders
        self.seconds_per_unit = full.exact(seconds_per_unit)
        if self.seconds_per_unit <= 0:
            raise ValueError('positive common physical clock unit required')

    def write(self, stop, measurement_report, *, programme_result, modes=('valid', 'valid')):
        if type(stop) is not stopped.StopSnapshot or stop.herald not in ('Psi+', 'Psi-'):
            raise ValueError('source-generated stopped BSM snapshot required')
        if type(programme_result) is not stopped.ProgrammeResult or not any(stop is item for item in programme_result.stops):
            raise ValueError('same generated complete stopped programme and shared error price required')
        if Q(measurement_report['upstream_error']) < programme_result.global_terminal_error:
            raise ValueError('measurement must retain the complete stopped instrument error price')
        burst = programme_result.source_record
        prior_phases = [segment for name in ('preparation', 'excitation', 'arrival_delay_phases', 'return_phases', 'recooling_phases')
                        for phase in burst[name] for segment in phase['raw_segments']]
        prior_phases += burst['gate']['source']['programmes']
        if any(rate for raw in prior_phases for rate in full.Segment.from_record(raw).ion_rates.values()):
            raise ValueError('premeasurement ionization requires a resolved source departure before the CEM writer')
        receipt = next((entry for entry in reversed(stop.journal) if entry.get('kind') == 'first-bsm-receipt'), None)
        if receipt is None or receipt.get('seconds_per_common_time_unit') != str(self.seconds_per_unit):
            raise ValueError('stopped event and writer must consume the same physical clock unit')
        source = measurement.PairMeasurementSource.from_record(measurement_report['raw_source'])
        source.verify(measurement_report)
        if (channel._input_record(stop.poststate_at_signal_return) != measurement_report['initial_state'] or
                stop.trap_histories != measurement_report['parent_trap_histories']):
            raise ValueError('record writer and measurement consume different stopped source states')
        if type(modes) is not tuple or len(modes) != 2 or any(mode not in MODES for mode in modes):
            raise ValueError('raw PC control modes required; comments are not loss labels')
        times = tuple(encoder.sample_at(stop.signal_return_time) for encoder in self.encoders)
        pulse_start = stop.signal_return_time
        wait = Q(0)
        first, second = source.compile(measurement_report['settings'])
        for a, b in zip(first.segments, second.segments):
            if any(segment.r*value for segment in (a, b) for value in segment.fields_r.values()) or any(
                    segment.c*value for segment in (a, b) for value in segment.fields_c.values()) or any(
                    rate for segment in (a, b) for rate in segment.ion_rates.values()):
                break
            wait += a.duration
        if max(time for time, _ in times) > pulse_start+wait:
            raise ValueError('raw atomic wait phases must cover both requested samples before active readout')
        pulse_end = pulse_start+Q(measurement_report['duration'])
        image = measurement_report['cem_image']
        outputs = []
        for outcome in source.detector.observations(image):
            clicks, fields = outcome['clicks'], []
            for side, (encoder, (_, uid), mode, setting) in enumerate(zip(
                    self.encoders, times, modes, measurement_report['settings'])):
                real_ms = encoder.unix_origin_ms+(pulse_end+encoder.write_latency)*self.seconds_per_unit*1000
                time_ms = real_ms.numerator//real_ms.denominator
                if time_ms < 0:
                    raise ValueError('raw writer emitted a negative Unix time')
                setting_token = encoder.setting_zero_token if setting == 0 else str(1-int(encoder.setting_zero_token))
                result = encoder.click_token if clicks[side] else str(1-int(encoder.click_token))
                flag, comment = MODES[mode]
                fields.append((Q(time_ms), setting_token, result, str(uid), stop.herald if side == 0 else None, flag, comment))
            journal = stop.journal+({'kind': 'raw-local-writer', 'raw_encoder_source': self.record(),
                                    'sample_times': tuple(time for time, _ in times), 'pulse_start': pulse_start,
                                    'pulse_end': pulse_end, 'settings': measurement_report['settings'],
                                    'CEM_receipt': image.receipt, 'clicks': clicks, 'control_modes': modes},)
            outputs.append(RecordBranch(clicks, tuple(fields), outcome['poststate'],
                                         source.detector.coarsen(image, clicks=clicks), journal,
                                         image.trace_norm_error))
        return tuple(outputs)

    def record(self):
        return {'schema': 'rb87-apparatus-local-writer-source/v1',
                'seconds_per_unit': str(self.seconds_per_unit), 'lab_encoders': [item.record() for item in self.encoders],
                'sample_request_policy': 'first local sample at or after signal return plus raw request latency',
                'measurement_start_policy': 'raw full-state programme starts at signal return; initial wait phases cover sample requests',
                'Unix_write_policy': 'floor milliseconds at raw measurement end plus side writer latency',
                'control_modes': {name: list(values) for name, values in MODES.items()},
                'herald_source': 'literal physical four-port BSM label; no old qubit h translation',
                'hidden_fragment_branches_marginalized': True, 'original_parser_owns_row_and_raw_SHA': True,
                'premature_ionization_policy': 'burst ion baths zero; general premeasurement departures need their source history',
                'actual_encoder_and_control_policy_identified': False, 'actual_hardware_uniquely_identified': False,
                'controller_advance': False}

    def write_all(self, programme_result, measurement_reports, *, modes=('valid', 'valid')):
        """One CP direct-sum consumer; pay shared stopping error once."""
        if (type(programme_result) is not stopped.ProgrammeResult or type(measurement_reports) is not tuple or
                len(measurement_reports) != len(programme_result.stops)):
            raise ValueError('all stopped source branches require their complete measurement reports')
        branches = []
        error = programme_result.global_terminal_error
        for stop, report in zip(programme_result.stops, measurement_reports):
            emitted = self.write(stop, report, programme_result=programme_result, modes=modes)
            branches.extend(emitted)
            # New local residual/substitution prices belong to this branch;
            # copied upstream terminal E belongs to the whole source instrument.
            local_error = Q(report['trace_norm_error'])-programme_result.global_terminal_error
            if local_error < 0:
                raise ValueError('local measurement price dropped shared stopping error')
            error += local_error
        return RecordImage(tuple(branches), programme_result.remaining_pair, error, self.record())

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get('schema') != 'rb87-apparatus-local-writer-source/v1':
            raise ValueError('raw local record writer source required')
        source = cls(tuple(LabEncoder(**item) for item in record['lab_encoders']),
                     seconds_per_unit=record['seconds_per_unit'])
        if source.record() != record:
            raise ValueError('raw encoder source identity or claim scope changed')
        return source


def bind_original_record(branch, observed_a, observed_b):
    """Restriction square on an emitted branch and two already paid original rows."""
    if type(branch) is not RecordBranch:
        raise ValueError('same-source generated record branch required')
    bound = []
    for fields, original in zip(branch.local_fields, (observed_a, observed_b)):
        if type(original) is not tuple or len(original) != len(history.FIELDS):
            raise ValueError('complete original nine-field observer required')
        time_ms = history.schema.timestamp(original[1], 'Unix-time')
        if (time_ms, *original[2:-1]) != fields:
            raise ValueError('generated programme fields differ from original observed restriction')
        bound.append(original)
    return {'original_observations': tuple(bound), 'source_branch': branch,
            'address_and_raw_sha_preserved': True, 'hardware_unique_identity_certified': False}
